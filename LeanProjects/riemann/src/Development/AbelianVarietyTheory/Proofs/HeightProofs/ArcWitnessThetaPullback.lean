import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.ThetaAlongCmp

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

end Comparison₂

section FirstPower

variable {X : Scheme.{0}} {L : LB X}

theorem gs_h0Sec {σ : Out.H0 L 1} {θ : L.Sec} (h : SectionOfLineBundleOne σ θ) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (k : L.ι)
    (hp : r z ∈ L.U k) :
    gs r z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)) (σ.f (fun _ => k)) = gs r z (L.U k) (θ.f k) := by
  have le : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) ≤ L.U k := fun y hy => Set.mem_iInter.1 hy 0
  rw [h (fun _ => k) le]
  exact gs_res r z le (Set.mem_iInter.2 fun _ => hp) _

theorem exists_section_of_h0 (σ : Out.H0 L 1) : ∃ θ : L.Sec, SectionOfLineBundleOne σ θ := by
  have le : ∀ k, L.U k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) := fun k y hy =>
    Set.mem_iInter.2 fun _ => hy
  refine ⟨⟨fun k => resG X (le k) (σ.f (fun _ => k)), fun i j => fn_ext fun y hy => ?_⟩, fun J hJ => ?_⟩
  · have m₁ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := le i hy.1
    have m₂ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := le j hy.2
    have gg := gm_linComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 X) y _ _ m₁ m₂
    rw [Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.id_comp] at gg
    refine (gs_res _ y _ hy _).trans ((gs_res _ y _ hy.1 _).trans ((gs_compat σ (𝟙 X) y m₁ m₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val gg.symm))
        ((gs_res _ y _ hy _).trans (gs_res _ y _ hy.2 _)))))))
  · obtain ⟨k, rfl⟩ : ∃ k, J = fun _ => k := ⟨J 0, funext fun i => congrArg J (Subsingleton.elim i 0)⟩
    refine fn_ext fun y hy => ?_
    have hy' : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) := hy
    exact ((gs_res (𝟙 X) y hJ hy' _).trans (gs_res (𝟙 X) y (le k) (hJ hy') _)).symm

end FirstPower

section Core

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} {B B₁ B₂ : Scheme.{0}} {t : SAB H B}
  {t₁ : SAB H B₁} {T : SAB H B₂} {f : Sp V ⟶ B} {p : B₁ ⟶ Xo.X} {q : B₁ ⟶ B₂} {χ : B ⟶ B₂} {u : Sp V ⟶ B₁}
  (m1 : SABMap G Xo.univ.t x) (m2 : SABMap G t f) (n0 : SABMap t₁ Xo.univ.t p) (n1 : SABMap t₁ T q)
  (n2 : SABMap t T χ) (m : SABMap G t₁ u)

def Thru (w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)) (w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ))
    (w₂ : LB.Iso t.PP.L (T.PP.L.pull n2.φ)) (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) (j : T.PP.L.ι) (k : t.PP.L.ι) (k₁ : t₁.PP.L.ι)
    (j₀ : Xo.univ.t.PP.L.ι), n1.φ (m.φ (r z)) ∈ T.PP.L.U j → m2.φ (r z) ∈ t.PP.L.U k →
    m.φ (r z) ∈ t₁.PP.L.U k₁ → m1.φ (r z) ∈ Xo.univ.t.PP.L.U j₀ →
    (gw w₁ (r ≫ m.φ) z j k₁).val * gs (r ≫ toGx m1) z _ (s.f (fun _ => j₀)) =
      (gw w₀ (r ≫ m.φ) z j₀ k₁).val * (gw w₂ (r ≫ m2.φ) z j k).val * gs (r ≫ m2.φ) z _ (θ.f k)

theorem tie_iff_thru (hG : Out.GlobalFnsSt) (hx : x = u ≫ p) (hu : u ≫ q = f ≫ χ) (e₁ : m1.φ = m.φ ≫ n0.φ)
    (e₂ : m.φ ≫ n1.φ = m2.φ ≫ n2.φ)
    {w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)} {w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ)}
    {w₂ : LB.Iso t.PP.L (T.PP.L.pull n2.φ)} (r₀ : RigIso n0 w₀) (r₁ : RigIso n1 w₁) (r₂ : RigIso n2 w₂)
    (θ : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) : Comparison₂ m1 m2 θ s ↔ Thru m1 m2 n0 n1 n2 m w₀ w₁ w₂ θ s := by
  obtain ⟨wm, rm⟩ := exists_rigIso m
  obtain ⟨W2, R2⟩ := exists_rigIso m2
  obtain ⟨W1, R1, T1⟩ := cube_rig_comp n0.cm m.cm m1.cm e₁ (by rw [m1.base, m.base, n0.base, hx]) _ _ _ w₀ wm r₀ rm
  obtain ⟨N, eN, WN, RN, TN⟩ := exists_comp_rig n1 m _ rfl r₁ rm
  obtain ⟨WN', RN', TN'⟩ := cube_rig_comp n2.cm m2.cm N.cm (eN.trans e₂)
    (by rw [N.base, m2.base, n2.base, hu]) _ _ _ w₂ W2 r₂ R2
  obtain rfl : WN = WN' := rigIso_unique N hG m1 RN RN'
  have sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) (j : T.PP.L.ι) (k : t.PP.L.ι) (k₁ : t₁.PP.L.ι)
      (i : G.PP.L.ι), n1.φ (m.φ (r z)) ∈ T.PP.L.U j → m2.φ (r z) ∈ t.PP.L.U k → m.φ (r z) ∈ t₁.PP.L.U k₁ →
      r z ∈ G.PP.L.U i → (gw w₁ (r ≫ m.φ) z j k₁).val * (gw wm r z k₁ i).val =
        (gw w₂ (r ≫ m2.φ) z j k).val * (gw W2 r z k i).val := fun Z r z j k k₁ i hj hk hk₁ hi => by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val ((TN Z r z j k₁ i hj hk₁ hi).symm.trans
      (TN' Z r z j k i ((congrArg (fun g => g (r z) ∈ T.PP.L.U j) eN).mpr hj) hk hi))
  constructor
  · rintro ⟨W1', W2', σ, R1', R2', a, b⟩ Z r z j k k₁ j₀ hj hk hk₁ hj₀
    obtain rfl : W1 = W1' := rigIso_unique m1 hG m1 R1 R1'
    obtain rfl : W2 = W2' := rigIso_unique m2 hG m1 R2 R2'
    obtain ⟨i, hi⟩ := exists_chart G.PP.isLB (r z)
    rw [a Z r z j₀ i hj₀ hi, b Z r z k i hk hi, T1 Z r z j₀ k₁ i hj₀ hk₁ hi, Units.val_mul]
    linear_combination (gw w₀ (r ≫ m.φ) z j₀ k₁).val * gs r z _ (σ.f i) * sq Z r z j k k₁ i hj hk hk₁ hi
  · intro h
    obtain ⟨σ, hσ⟩ := sec_pull_down ((isGen_iff W2).1 R2.1) t.PP.isLB G.PP.isLB θ
    refine ⟨W1, W2, σ, R1, R2, fun Z r z j₀ i hj₀ hi => ?_, hσ⟩
    obtain ⟨j, hj⟩ := exists_chart T.PP.isLB (n1.φ (m.φ (r z)))
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (m2.φ (r z))
    obtain ⟨k₁, hk₁⟩ := exists_chart t₁.PP.isLB (m.φ (r z))
    have e := h Z r z j k k₁ j₀ hj hk hk₁ hj₀
    rw [hσ Z r z k i hk hi] at e
    refine (Units.mul_right_inj (gw w₁ (r ≫ m.φ) z j k₁)).1 (e.trans ?_)
    rw [T1 Z r z j₀ k₁ i hj₀ hk₁ hi, Units.val_mul]
    linear_combination -(gw w₀ (r ≫ m.φ) z j₀ k₁).val * gs r z _ (σ.f i) * sq Z r z j k k₁ i hj hk hk₁ hi

def OnOpens (L : RigLB t.G) (g₁ : Gx x ⟶ t₁.G.left) (g₂ : Gx x ⟶ t.G.left)
    (w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)) (w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ))
    (w₂ : LB.Iso L.L (T.PP.L.pull n2.φ)) (σ : Out.H0 L.L 1) (s : LB.Sec (PPx x)) : Prop :=
  ∀ (j : T.PP.L.ι) (k : L.L.ι) (k₁ : t₁.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι) (U : (Gx x).Opens)
    (h₀ : U ≤ g₁ ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull n0.φ) t₁.PP.L).U (fun _ => j₀, k₁))
    (h₁ : U ≤ g₁ ⁻¹ᵁ (LB.div (T.PP.L.pull n1.φ) t₁.PP.L).U (fun _ => j, k₁))
    (h₂ : U ≤ g₂ ⁻¹ᵁ (LB.div (T.PP.L.pull n2.φ) L.L).U (fun _ => j, k))
    (h₃ : U ≤ g₂ ⁻¹ᵁ LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k))
    (h₄ : U ≤ (PPx x).U (fun _ => j₀)),
    (g₁.appLE _ _ h₁).hom (w₁.s (fun _ => j, k₁)).val * resG _ h₄ (s.f (fun _ => j₀)) =
      (g₁.appLE _ _ h₀).hom (w₀.s (fun _ => j₀, k₁)).val * (g₂.appLE _ _ h₂).hom (w₂.s (fun _ => j, k)).val *
        (g₂.appLE _ _ h₃).hom (σ.f (fun _ => k))

theorem gs_onOpens {g₁ : Gx x ⟶ t₁.G.left} {g₂ : Gx x ⟶ t.G.left}
    {w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)} {w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ)}
    {w₂ : LB.Iso t.PP.L (T.PP.L.pull n2.φ)} {σ : Out.H0 t.PP.L 1} {θ : LB.Sec t.PP.L} (hσ : SectionOfLineBundleOne σ θ)
    (s : LB.Sec (PPx x)) (j : T.PP.L.ι) (k : t.PP.L.ι) (k₁ : t₁.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι) (U : (Gx x).Opens)
    (h₀ : U ≤ g₁ ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull n0.φ) t₁.PP.L).U (fun _ => j₀, k₁))
    (h₁ : U ≤ g₁ ⁻¹ᵁ (LB.div (T.PP.L.pull n1.φ) t₁.PP.L).U (fun _ => j, k₁))
    (h₂ : U ≤ g₂ ⁻¹ᵁ (LB.div (T.PP.L.pull n2.φ) t.PP.L).U (fun _ => j, k))
    (h₃ : U ≤ g₂ ⁻¹ᵁ LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k))
    (h₄ : U ≤ (PPx x).U (fun _ => j₀)) {Z : Scheme.{0}} (r : Z ⟶ Gx x) (z : Z) (hz : r z ∈ U) :
    gs r z U ((g₁.appLE _ _ h₁).hom (w₁.s (fun _ => j, k₁)).val * resG _ h₄ (s.f (fun _ => j₀))) =
        (gw w₁ (r ≫ g₁) z j k₁).val * gs r z _ (s.f (fun _ => j₀)) ∧
      gs r z U ((g₁.appLE _ _ h₀).hom (w₀.s (fun _ => j₀, k₁)).val *
          (g₂.appLE _ _ h₂).hom (w₂.s (fun _ => j, k)).val * (g₂.appLE _ _ h₃).hom (σ.f (fun _ => k))) =
        (gw w₀ (r ≫ g₁) z j₀ k₁).val * (gw w₂ (r ≫ g₂) z j k).val * gs (r ≫ g₂) z _ (θ.f k) :=
  ⟨(gs_mul r z U hz _ _).trans (congrArg₂ (· * ·)
      ((gs_appLE g₁ _ _ h₁ r z hz _).trans (gs_unit (r ≫ g₁) z _ (h₁ hz) _)) (gs_res r z h₄ hz _)),
    (gs_mul r z U hz _ _).trans (congrArg₂ (· * ·) ((gs_mul r z U hz _ _).trans (congrArg₂ (· * ·)
      ((gs_appLE g₁ _ _ h₀ r z hz _).trans (gs_unit (r ≫ g₁) z _ (h₀ hz) _))
      ((gs_appLE g₂ _ _ h₂ r z hz _).trans (gs_unit (r ≫ g₂) z _ (h₂ hz) _))))
      ((gs_appLE g₂ _ _ h₃ r z hz _).trans (gs_h0Sec hσ (r ≫ g₂) z k (h₂ hz).2)))⟩

theorem onOpens_iff_thru (e₁ : m1.φ = m.φ ≫ n0.φ) (e₂ : m.φ ≫ n1.φ = m2.φ ≫ n2.φ) {h : Gx x ⟶ G.G.left}
    (hφ : h ≫ m1.φ = (snd (Over.mk x) Xo.univ.t.G).left) (hg : toGx m1 ≫ h = 𝟙 _) (hg' : h ≫ toGx m1 = 𝟙 _)
    {w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)} {w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ)}
    {w₂ : LB.Iso t.PP.L (T.PP.L.pull n2.φ)} {σ : Out.H0 t.PP.L 1} {θ : LB.Sec t.PP.L} (hσ : SectionOfLineBundleOne σ θ)
    (s : LB.Sec (PPx x)) :
    OnOpens n0 n1 n2 t.PP (h ≫ m.φ) (h ≫ m2.φ) w₀ w₁ w₂ σ s ↔ Thru m1 m2 n0 n1 n2 m w₀ w₁ w₂ θ s := by
  constructor
  · intro a Z r z j k k₁ j₀ hj hk hk₁ hj₀
    have c₁ : (r ≫ toGx m1) ≫ h ≫ m.φ = r ≫ m.φ := by rw [Category.assoc, reassoc_of% hg]
    have c₂ : (r ≫ toGx m1) ≫ h ≫ m2.φ = r ≫ m2.φ := by rw [Category.assoc, reassoc_of% hg]
    have d₁ : (h ≫ m.φ) ((r ≫ toGx m1) z) = m.φ (r z) := congrArg (fun g => g z) c₁
    have d₂ : (h ≫ m2.φ) ((r ≫ toGx m1) z) = m2.φ (r z) := congrArg (fun g => g z) c₂
    let U : (Gx x).Opens :=
      ((h ≫ m.φ) ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull n0.φ) t₁.PP.L).U (fun _ => j₀, k₁) ⊓
        (h ≫ m.φ) ⁻¹ᵁ (LB.div (T.PP.L.pull n1.φ) t₁.PP.L).U (fun _ => j, k₁)) ⊓
      (((h ≫ m2.φ) ⁻¹ᵁ (LB.div (T.PP.L.pull n2.φ) t.PP.L).U (fun _ => j, k) ⊓
        (h ≫ m2.φ) ⁻¹ᵁ LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) ⊓ (PPx x).U (fun _ => j₀))
    have p₀ : m.φ (r z) ∈ (LB.div (Xo.univ.t.PP.L.pull n0.φ) t₁.PP.L).U (fun _ => j₀, k₁) :=
      ⟨mem_pull.2 ((congrArg (fun g => g (r z) ∈ Xo.univ.t.PP.L.U j₀) e₁).mp hj₀), hk₁⟩
    have p₁ : m.φ (r z) ∈ (LB.div (T.PP.L.pull n1.φ) t₁.PP.L).U (fun _ => j, k₁) := ⟨mem_pull.2 hj, hk₁⟩
    have p₂ : m2.φ (r z) ∈ (LB.div (T.PP.L.pull n2.φ) t.PP.L).U (fun _ => j, k) :=
      ⟨mem_pull.2 ((congrArg (fun g => g (r z) ∈ T.PP.L.U j) e₂).mp hj), hk⟩
    have p₃ : m2.φ (r z) ∈ LB.wchart t.PP.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k) :=
      Set.mem_iInter.2 fun _ => hk
    rw [← d₁] at p₀ p₁
    rw [← d₂] at p₂ p₃
    have hz : (r ≫ toGx m1) z ∈ U := ⟨⟨p₀, p₁⟩, ⟨p₂, p₃⟩, le_toGx m1 j₀ hj₀⟩
    have h₀ : U ≤ _ := inf_le_left.trans inf_le_left
    have h₁ : U ≤ _ := inf_le_left.trans inf_le_right
    have h₂ : U ≤ _ := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have h₃ : U ≤ _ := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have h₄ : U ≤ _ := inf_le_right.trans inf_le_right
    obtain ⟨b₁, b₂⟩ := gs_onOpens n0 n1 n2 (w₀ := w₀) (w₁ := w₁) (w₂ := w₂) hσ s j k k₁ j₀ U h₀ h₁ h₂ h₃ h₄ _ z hz
    rw [c₁] at b₁
    rw [c₁, c₂] at b₂
    exact b₁.symm.trans ((congrArg (gs _ z U) (a j k k₁ j₀ U h₀ h₁ h₂ h₃ h₄)).trans b₂)
  · intro a j k k₁ j₀ U h₀ h₁ h₂ h₃ h₄
    refine fn_ext fun y hy => ?_
    obtain ⟨b₁, b₂⟩ := gs_onOpens n0 n1 n2 (w₀ := w₀) (w₁ := w₁) (w₂ := w₂) hσ s j k k₁ j₀ U h₀ h₁ h₂ h₃ h₄
      (𝟙 _) y hy
    have e := a _ h y j k k₁ j₀ (mem_pull.1 (h₁ hy).1) (h₂ hy).2 (h₁ hy).2
      ((congrArg (fun g => g y ∈ Xo.univ.t.PP.L.U j₀) hφ).mpr (Set.mem_iInter.1 (h₄ hy) 0))
    rw [hg'] at e
    rw [Category.id_comp] at b₁
    rw [Category.id_comp, Category.id_comp] at b₂
    exact b₁.trans (e.trans b₂.symm)

theorem tie_iff_onOpens (hG : Out.GlobalFnsSt) (hx : x = u ≫ p) (hu : u ≫ q = f ≫ χ) (e₁ : m1.φ = m.φ ≫ n0.φ)
    (e₂ : m.φ ≫ n1.φ = m2.φ ≫ n2.φ) (L : RigLB t.G) (hL : L = t.PP) (Q : Out.H0 L.L 1 → Prop)
    (s : LB.Sec (PPx x)) :
    (∃ θ : LB.Sec t.PP.L, (∃ (σ : Out.H0 L.L 1) (θ' : LB.Sec L.L), Q σ ∧ SectionOfLineBundleOne σ θ' ∧ HEq θ θ') ∧ Comparison₂ m1 m2 θ s) ↔
      ∃ (σ : Out.H0 L.L 1) (g₁ : Gx x ⟶ t₁.G.left) (g₂ : Gx x ⟶ t.G.left) (w₂ : LB.Iso L.L (T.PP.L.pull n2.φ))
        (w₁ : LB.Iso t₁.PP.L (T.PP.L.pull n1.φ)) (w₀ : LB.Iso t₁.PP.L (Xo.univ.t.PP.L.pull n0.φ)),
        Q σ ∧ g₁ ≫ n0.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
        g₁ ≫ t₁.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ u ∧
        g₂ ≫ n2.φ = g₁ ≫ n1.φ ∧ g₂ ≫ t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ f ∧
        IsRigIso n2.cm L T.PP w₂ ∧ IsRigIso n1.cm t₁.PP T.PP w₁ ∧ IsRigIso n0.cm t₁.PP Xo.univ.t.PP w₀ ∧
        OnOpens n0 n1 n2 L g₁ g₂ w₀ w₁ w₂ σ s := by
  subst hL
  obtain ⟨h, hφ, hh, hg, hg'⟩ := exists_inv m1
  have a₁ : (h ≫ m.φ) ≫ n0.φ = (snd (Over.mk x) Xo.univ.t.G).left := by rw [Category.assoc, ← e₁, hφ]
  have a₂ : (h ≫ m.φ) ≫ t₁.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ u := by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, hh]
  have a₃ : (h ≫ m2.φ) ≫ n2.φ = (h ≫ m.φ) ≫ n1.φ := by rw [Category.assoc, Category.assoc, e₂]
  have a₄ : (h ≫ m2.φ) ≫ t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ f := by
    rw [Category.assoc, m2.cart.1.w, ← Category.assoc, hh]
  constructor
  · rintro ⟨θ, ⟨σ, θ', hQ, hσ, he⟩, hT⟩
    cases he
    obtain ⟨w₀, r₀⟩ := exists_rigIso n0
    obtain ⟨w₁, r₁⟩ := exists_rigIso n1
    obtain ⟨w₂, r₂⟩ := exists_rigIso n2
    exact ⟨σ, h ≫ m.φ, h ≫ m2.φ, w₂, w₁, w₀, hQ, a₁, a₂, a₃, a₄, r₂, r₁, r₀,
      (onOpens_iff_thru m1 m2 n0 n1 n2 m e₁ e₂ hφ hg hg' hσ s).2
        ((tie_iff_thru m1 m2 n0 n1 n2 m hG hx hu e₁ e₂ r₀ r₁ r₂ θ s).1 hT)⟩
  · rintro ⟨σ, g₁, g₂, w₂, w₁, w₀, hQ, b₁, b₂, b₃, b₄, r₂, r₁, r₀, hO⟩
    obtain rfl : g₁ = h ≫ m.φ := n0.cart.1.hom_ext (b₁.trans a₁.symm) (b₂.trans a₂.symm)
    obtain rfl : g₂ = h ≫ m2.φ := n2.cart.1.hom_ext (b₃.trans a₃.symm) (b₄.trans a₄.symm)
    obtain ⟨θ, hσ⟩ := exists_section_of_h0 σ
    exact ⟨θ, ⟨σ, θ, hQ, hσ, HEq.rfl⟩, (tie_iff_thru m1 m2 n0 n1 n2 m hG hx hu e₁ e₂ r₀ r₁ r₂ θ s).2
      ((onOpens_iff_thru m1 m2 n0 n1 n2 m e₁ e₂ hφ hg hg' hσ s).1 hO)⟩

end Core

end GlobalTheory.ArcQ.ThetaAlongCmp

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

theorem thetaClause_iff_thetaAlong : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (S : Type) [CommRing S] (ι : PowerSeries A →+* S) (x : Sp S ⟶ Xo.X) (z : Sp S ⟶ Xo.XF c) (t' : SAB H (Sp S)) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' W.t (spMap ι)) (φ : t'.G.left ⟶ Y.oF.t.G.left) (s : LB.Sec (PPx x)), z ≫ Y.j = spMap ι ≫ χ → z ≫ pullback.fst _ _ = x → φ ≫ Y.oF.t.G.hom = t'.G.hom ≫ z → φ ≫ Y.m0.toSABMap.φ = m1.φ → φ ≫ Y.m.φ = m2.φ ≫ W.m.φ → ((∃ (θ : LB.Sec W.t.PP.L) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (W.t.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)), ThetaOf W th θ ∧ RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.ThetaAlong W ι z th s) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ b a χ W th S _ ι x z t' m1 m2 φ s hj hx φb φ1 φ2
  subst hx
  obtain ⟨m, e₁⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ z Y.m0.toSABMap m1
  obtain rfl : φ = m.φ := Y.m0.toSABMap.cart.1.hom_ext (φ1.trans e₁) (φb.trans m.cart.1.w.symm)
  refine Iff.trans ?_ (ThetaAlongCmp.tie_iff_onOpens m1 m2 Y.m0.toSABMap Y.m W.m m hG rfl hj e₁ φ2 W.P.U.LG
    W.P.bundle (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.ThetaId W th) s)
  refine exists_congr fun θ => ?_
  rw [← ThetaAlongCmp.tie_iff]
  constructor
  · rintro ⟨w1, w2, σ', s1, θ2, ⟨σ, fam, θ', h1, h2, h3, h4⟩, hT⟩
    exact ⟨⟨σ, θ', ⟨fam, h1, h2⟩, h3, h4⟩, w1, w2, σ', s1, θ2, hT⟩
  · rintro ⟨⟨σ, θ', ⟨fam, h1, h2⟩, h3, h4⟩, w1, w2, σ', s1, θ2, hT⟩
    exact ⟨w1, w2, σ', s1, θ2, ⟨σ, fam, θ', h1, h2, h3, h4⟩, hT⟩

end GlobalTheory.ArcQ
