import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOfStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.FrUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

def Comparison₂ {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} {B : Scheme.{0}} {t : SAB H B} {f : Sp V ⟶ B}
    (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t f) (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) : Prop :=
  ∃ (w1 : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso G.PP.L (t.PP.L.pull m2.φ)) (σ : LB.Sec G.PP.L),
    RigIso m1 w1 ∧ RigIso m2 w2 ∧ SecRel m1 w1 s σ ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) j k, m2.φ (r z) ∈ t.PP.L.U j → r z ∈ G.PP.L.U k →
      gs (r ≫ m2.φ) z _ (θ.f j) = (gw w2 r z j k).val * gs r z _ (σ.f k)

section Comparison₂

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} {B : Scheme.{0}} {t : SAB H B} {f : Sp V ⟶ B}
  (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t f) (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x))

theorem tie_iff : (∃ (w1 : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso G.PP.L (t.PP.L.pull m2.φ))
      (σ' : LB.Sec G.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (t.PP.L.pull m2.φ)),
      RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧
      ∀ g : G.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk x) Xo.univ.t.G).left = G.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ↔ Comparison₂ m1 m2 θ s := by
  constructor
  · rintro ⟨w1, w2, σ, s1, θ2, r1, r2, i1, i2, p, c⟩
    refine ⟨w1, w2, σ, r1, r2, fun Z r z j k hj hk => ?_, fun Z r z j k hj hk => ?_⟩
    · have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => j) ≤ toGx m1 ⁻¹ᵁ (PPx x).U (fun _ => j) :=
        fun q hq => le_toGx m1 j (mem_pull.1 hq)
      refine Eq.trans ?_ ((isoMaps_iff w1 σ s1).1 i1 Z r z j k hj hk)
      rw [c (toGx m1) (toGx_snd m1) (toGx_fst m1) (fun _ => j) le]
      exact (gs_appLE (toGx m1) _ _ le r z (mem_pull.2 hj) _).symm
    · have le : (t.PP.L.pull m2.φ).U (fun _ => j) ≤ m2.φ ⁻¹ᵁ t.PP.L.U j := fun q hq => mem_pull.1 hq
      refine Eq.trans ?_ ((isoMaps_iff w2 σ θ2).1 i2 Z r z j k hj hk)
      rw [p (fun _ => j) le]
      exact (gs_appLE m2.φ _ _ le r z (mem_pull.2 hj) _).symm
  · rintro ⟨w1, w2, σ, r1, r2, a, b⟩
    obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w1).1 r1.1) Xo.univ.t.PP.isLB G.PP.isLB σ
    refine ⟨w1, w2, σ, s1, thfPull t.PP.L m2.φ θ, r1, r2,
      (isoMaps_iff w1 σ s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk,
      (isoMaps_iff w2 σ _).2 fun Z r z j k hj hk =>
        (gs_appLE m2.φ _ _ _ r z (mem_pull.2 hj) _).trans (b Z r z j k hj hk), fun _ _ => rfl, ?_⟩
    intro g e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    have eg : g = toGx m1 := by
      apply FramedBaseChange.pulledGroup_hom_ext
      · rw [e₁, toGx_snd]
      · rw [e₂, toGx_fst]
    subst eg
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart G.PP.isLB p
    rw [hs1 _ (𝟙 _) p J k hp hk, gs_appLE _ _ _ hJ (𝟙 _) p hp, a _ (𝟙 _) p _ k (mem_pull.1 hp) hk]

theorem rigIso_unique (hG : Out.GlobalFnsSt) {w w' : LB.Iso G.PP.L (t.PP.L.pull m2.φ)} (m1 : SABMap G Xo.univ.t x)
    (h : RigIso m2 w) (h' : RigIso m2 w') : w = w' := by
  have hp : IsProper G.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  have hab : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hp, G.semi.geomConnected⟩
  exact GlobalTheory.iso_eq_of_maps_along_section (S := Sp V) (exists_chart G.PP.isLB)
    (fun y => (exists_chart t.PP.isLB (m2.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    G.G.hom (eSec G.G) (Over.w η[G.G]) (hG _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem tie_unique (hG : Out.GlobalFnsSt) {s s' : LB.Sec (PPx x)} (h : Comparison₂ m1 m2 θ s) (h' : Comparison₂ m1 m2 θ s') :
    s = s' := by
  obtain ⟨w1, w2, σ, r1, r2, a, b⟩ := h
  obtain ⟨w1', w2', σ', r1', r2', a', b'⟩ := h'
  obtain rfl : w1 = w1' := rigIso_unique m1 hG m1 r1 r1'
  obtain rfl : w2 = w2' := rigIso_unique m2 hG m1 r2 r2'
  have hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) k, r z ∈ G.PP.L.U k →
      gs r z _ (σ.f k) = gs r z _ (σ'.f k) := fun Z r z k hk => by
    obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m2.φ (r z))
    exact (Units.mul_right_inj _).1 ((b Z r z j k hj hk).symm.trans (b' Z r z j k hj hk))
  obtain ⟨h, hφ, -, -, h0g⟩ := exists_inv m1
  have : ∀ i, s.f i = s'.f i := by
    intro (i : Fin 1 → Xo.univ.t.PP.L.ι)
    obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
    refine fn_ext fun y hy => ?_
    have mφ : m1.φ (h y) ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) hφ).mpr (Set.mem_iInter.1 hy 0)
    obtain ⟨k, hk⟩ := exists_chart G.PP.isLB (h y)
    have e := (a _ h y j k mφ hk).trans ((congrArg _ (hσ _ h y k hk)).trans (a' _ h y j k mφ hk).symm)
    rwa [h0g] at e
  cases s
  cases s'
  congr 1
  exact funext this

theorem tie_pull {V' : Type} [CommRing V'] {x' : Sp V' ⟶ Xo.X} {G' : SAB H (Sp V')} {f' : Sp V' ⟶ B}
    {g : Sp V' ⟶ Sp V} (n : SABMap G' G g) (m1' : SABMap G' Xo.univ.t x') (m2' : SABMap G' t f')
    (hx : x' = g ≫ x) (hf : f' = g ≫ f) (e₁ : m1'.φ = n.φ ≫ m1.φ) (e₂ : m2'.φ = n.φ ≫ m2.φ)
    (s' : LB.Sec (PPx x')) (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (hb : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ g)
    (ha : ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x') (z : Z) (j : Xo.univ.t.PP.L.ι), r z ∈ (PPx x').U (fun _ => j) →
      gs r z _ (s'.f (fun _ => j)) = gs (r ≫ pm) z _ (s.f (fun _ => j)))
    (h : Comparison₂ m1 m2 θ s) : Comparison₂ m1' m2' θ s' := by
  obtain ⟨w1, w2, σ, r1, r2, a, b⟩ := h
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨w1', r1', T1⟩ := cube_rig_comp m1.cm n.cm m1'.cm e₁ (by rw [m1'.base, n.base, m1.base, hx]) _ _ _ w1 w0 r1 r0
  obtain ⟨w2', r2', T2⟩ := cube_rig_comp m2.cm n.cm m2'.cm e₂ (by rw [m2'.base, n.base, m2.base, hf]) _ _ _ w2 w0 r2 r0
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 r0.1) G.PP.isLB G'.PP.isLB σ
  refine ⟨w1', w2', σ', r1', r2', fun Z r z j k hj hk => ?_, fun Z r z j k hj hk => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart G.PP.isLB (n.φ (r z))
    have hm : m1.φ ((r ≫ n.φ) z) ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (fun q => q (r z) ∈ Xo.univ.t.PP.L.U j) e₁).mp hj
    have eg : (r ≫ toGx m1') ≫ pm = (r ≫ n.φ) ≫ toGx m1 := by
      rw [Category.assoc, Category.assoc]
      congr 1
      apply FramedBaseChange.pulledGroup_hom_ext
      · rw [Category.assoc, hs, toGx_snd, e₁, Category.assoc, toGx_snd]
      · rw [Category.assoc, hb, ← Category.assoc, toGx_fst, Category.assoc, toGx_fst]
        exact n.cart.1.w.symm
    rw [ha Z (r ≫ toGx m1') z j (le_toGx m1' j hj), eg, a Z (r ≫ n.φ) z j i hm hi, hσ' Z r z i k hi hk,
      T1 Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc]
  · obtain ⟨i, hi⟩ := exists_chart G.PP.isLB (n.φ (r z))
    have hm : m2.φ ((r ≫ n.φ) z) ∈ t.PP.L.U j :=
      (congrArg (fun q => q (r z) ∈ t.PP.L.U j) e₂).mp hj
    have eg : r ≫ m2'.φ = (r ≫ n.φ) ≫ m2.φ := by rw [e₂, Category.assoc]
    refine (congrArg (fun q => gs q z _ (θ.f j)) eg).trans ?_
    rw [b Z (r ≫ n.φ) z j i hm hi, hσ' Z r z i k hi hk,
      T2 Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc]

end Comparison₂

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← FramedBaseChange.spec_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

variable {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {A : Type} [CommRing A] [IsDomain A]
  {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}

theorem mono_m (hj : Mono Y.j) : Mono Y.m.φ :=
  MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _) Y.m.cart.1.flip hj

theorem unique (W : Wit Y a χ) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec)
    (hG : Out.GlobalFnsSt) (hv : ∀ τ k v v', LieImg W (e τ k) v → LieImg W (e τ k) v' → v = v')
    (hθ : ∀ θ θ', ThetaOf W th θ → ThetaOf W th θ' → θ = θ')
    {S : Type} [CommRing S] [Algebra c.F S] (io : PowerSeries A →+* S) (y y' : FrPt Xo c S) (hj : Mono Y.j)
    (h : IsArcFr W e th io y) (h' : IsArcFr W e th io y') : y' = y := by
  obtain ⟨x, xo, u, t1, t2, t3, s, t4⟩ := y
  obtain ⟨x', xo', u', t1', t2', t3', s', t4'⟩ := y'
  obtain ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hth, hT⟩ := h
  obtain ⟨z', G', m1', m2', φ', zj', zx', φb', φ1', φ2', hu', θ', w1', w2', σ', s1', θ2', hth', hT'⟩ := h'
  dsimp only at *
  obtain rfl : z = z' := (cancel_mono Y.j).1 (zj.trans zj'.symm)
  obtain rfl : x = x' := zx.symm.trans zx'
  obtain rfl : θ = θ' := hθ _ _ hth hth'
  have := mono_m hj
  obtain rfl : u = u' := by
    funext τ k
    obtain ⟨v, p, h1, h2, h3, -⟩ := hu τ k
    obtain ⟨v', p', h1', h2', h3', -⟩ := hu' τ k
    obtain rfl : v = v' := hv τ k _ _ h1 h1'
    have : p ≫ φ = p' ≫ φ' := by
      rw [← cancel_mono Y.m.φ, Category.assoc, Category.assoc, φ2, φ2', ← Category.assoc, ← Category.assoc, h3, h3']
    rw [← h2, ← h2', ← φ1, ← φ1', ← Category.assoc, ← Category.assoc, this]
  have T := (tie_iff m1 m2 θ s).1 ⟨w1, w2, σ, s1, θ2, hT⟩
  have T' := (tie_iff m1' m2' θ s').1 ⟨w1', w2', σ', s1', θ2', hT'⟩
  obtain ⟨n, e₁⟩ := exists_over_id (Category.id_comp x).symm m1 m1'
  have nb : n.φ ≫ G.G.hom = G'.G.hom := n.cart.1.w.trans (Category.comp_id _)
  have e₀ : φ' = n.φ ≫ φ := by
    apply Y.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc]
      exact φ1'.trans (e₁.trans (congrArg _ φ1.symm))
    · rw [Category.assoc, φb, φb', ← Category.assoc, nb]
  have e₂ : m2'.φ = n.φ ≫ m2.φ := by
    apply W.m.cart.1.hom_ext
    · rw [Category.assoc]
      exact φ2'.symm.trans (by rw [e₀, Category.assoc]; exact congrArg _ φ2)
    · rw [Category.assoc, m2.cart.1.w, m2'.cart.1.w, ← Category.assoc, nb]
  have T'' := tie_pull m1 m2 θ s n m1' m2' (Category.id_comp x).symm (Category.id_comp _).symm e₁ e₂ s (𝟙 _)
    (Category.id_comp _) ((Category.id_comp _).trans (Category.comp_id _).symm)
    (fun Z r z j _ => by rw [Category.comp_id]) T
  obtain rfl : s = s' := tie_unique m1' m2' θ hG T'' T'
  rfl

theorem baseChange (W : Wit Y a χ) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A))
    (th : a.D₀.P.L.Sec) {S : Type} [CommRing S] [Algebra c.F S] (io : PowerSeries A →+* S) (y : FrPt Xo c S)
    (h : IsArcFr W e th io y) {T : Type} [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y₁ : FrPt Xo c T) (hm : FrMap ψ y y₁) : IsArcFr W e th (ψ.toRingHom.comp io) y₁ := by
  obtain ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hth, hT⟩ := h
  obtain ⟨hx, hu₁, pm, hs, hf, ha⟩ := hm
  obtain ⟨G', ⟨n⟩⟩ : ∃ G' : SAB H (Sp T), Nonempty (SABMap G' G (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) G
    exact ⟨_, ⟨m⟩⟩
  have hio : spMap (ψ.toRingHom.comp io) = spMap ψ.toRingHom ≫ spMap io := FramedBaseChange.spec_comp _ _
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨m1', e₁, -⟩ := exists_comp_rig m1 n y₁.x hx hT.1 r0
  obtain ⟨m2', e₂, -⟩ := exists_comp_rig m2 n _ hio hT.2.1 r0
  have T₀ := (tie_iff m1 m2 θ y.s).1 ⟨w1, w2, σ, s1, θ2, hT⟩
  have T₁ := tie_pull m1 m2 θ y.s n m1' m2' hx hio e₁ e₂ y₁.s pm hs hf (fun Z r z j hz => by
    have hle := FramedBaseChange.chart_le pm hs (fun _ => j)
    rw [← ha _ hle, gs_appLE pm _ _ hle r z hz]) T₀
  obtain ⟨w1', w2', σ', s1', θ2', hT'⟩ := (tie_iff m1' m2' θ y₁.s).2 T₁
  refine ⟨spMap ψ.toRingHom ≫ z, G', m1', m2', n.φ ≫ φ, ?_, ?_, ?_, ?_, ?_, fun τ k => ?_,
    θ, w1', w2', σ', s1', θ2', hth, hT'⟩
  · rw [Category.assoc, zj, hio, Category.assoc]
  · rw [Category.assoc, zx, hx]
  · rw [Category.assoc, φb, ← Category.assoc, n.cart.1.w, Category.assoc]
  · rw [Category.assoc, φ1, e₁]
  · rw [Category.assoc, φ2, e₂, Category.assoc]
  · obtain ⟨v, p, h1, h2, h3, h4⟩ := hu τ k
    have cond : (spMap (dualMap ψ.toRingHom) ≫ p) ≫ G.G.hom =
        spMap (algebraMap T (DualNumber T)) ≫ spMap ψ.toRingHom := by
      rw [Category.assoc, h4, dual_alg]
    refine ⟨v, n.cart.1.lift _ _ cond, h1, ?_, ?_, n.cart.1.lift_snd _ _ cond⟩
    · rw [e₁, ← Category.assoc, n.cart.1.lift_fst _ _ cond, Category.assoc, h2, hu₁]
    · rw [e₂, ← Category.assoc, n.cart.1.lift_fst _ _ cond, Category.assoc, h3, dual_comp, Category.assoc]

end GlobalTheory.ArcQ.FrUniq

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem isArcFr_unique_baseChange : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ThNZ th → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι : PowerSeries A →+* S) (y : FrPt Xo c S), IsArcFr W e th ι y → (Mono Y.j → ∀ y', IsArcFr W e th ι y' → y' = y) ∧ (Mono Y.j → ∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y₁ : FrPt Xo c T), FrMap φ y y₁ → IsArcFr W e th (φ.toRingHom.comp ι) y₁) := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W e th hth S _ _ ι y hy
  refine ⟨fun hj y' hy' => FrUniq.unique W e th hL.globalFns (fun τ k v v' => ?_) (fun θ θ' => ?_) ι y y' hj hy hy',
    fun _ T _ _ φ y₁ hm => FrUniq.baseChange W e th ι y hy φ y₁ hm⟩
  · exact (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c O β Y A b a χ W (e τ k)).1.unique
  · exact (GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O β Y A b a χ W th hth).1.unique

end GlobalTheory.ArcQ
