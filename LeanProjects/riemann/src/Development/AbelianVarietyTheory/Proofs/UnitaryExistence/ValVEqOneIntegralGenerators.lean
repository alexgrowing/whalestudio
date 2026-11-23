import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.IntegralGenerator

section Calc

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem isoMaps_pt {w : LB.Iso L' (L.pull F)} {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} (h : IsoMaps w σ s)
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have hm : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have e := congrArg (gs r z _) (h (fun _ => j) k)
  exact (gs_res r z _ hm _).symm.trans (e.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem pullSec_pt {s : LB.Sec L} {s' : LB.Sec (L.pull F)} (h : PullSec F s s')
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (hj : F (r z) ∈ L.U j) :
    gs r z _ (s'.f (fun _ => j)) = gs (r ≫ F) z _ (s.f j) :=
  (congrArg (gs r z _) (h (fun _ => j) (LB.wchart_le L _ _ PUnit.unit))).trans
    (gs_appLE F _ _ _ r z (mem_pull.2 hj) _)

theorem exists_sec_along (ρ : X ⟶ X') (e : ρ ≫ F = 𝟙 X) (s : LB.Sec (L.pull F)) :
    ∃ τ : LB.Sec L, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : L.ι), r z ∈ L.U j →
      gs r z _ (τ.f j) = gs (r ≫ ρ) z _ (s.f (fun _ => j)) := by
  have le : ∀ j, L.U j ≤ ρ ⁻¹ᵁ (L.pull F).U (fun _ => j) := fun j y hy =>
    mem_pull.2 ((congrArg (fun q => q y ∈ L.U j) e).mpr hy)
  refine ⟨⟨fun j => (ρ.appLE _ _ (le j)).hom (s.f (fun _ => j)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z j hj => gs_appLE ρ _ _ (le j) r z hj _⟩
  have h₁ : (𝟙 X ≫ ρ) y ∈ (L.pull F).U (fun _ => j) := le j hy.1
  have h₂ : (𝟙 X ≫ ρ) y ∈ (L.pull F).U (fun _ => j') := le j' hy.2
  have g := gm_pull_g L F (𝟙 X ≫ ρ) y _ _ h₁ h₂
  rw [Category.assoc, e, Category.comp_id] at g
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, gs_appLE ρ _ _ _ _ y hy.1,
    gs_appLE ρ _ _ _ _ y hy.2, gs_compat s _ y h₁ h₂, g]

theorem exists_unit_of_iso {V : Type} [CommRing V] (p : X ⟶ Sp V) (p' : X' ⟶ Sp V) (hp : F ≫ p = p') [IsIso F]
    (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w) (θ : LB.Sec L) (θ' : LB.Sec L')
    (hθ : ∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn p _ a * θ.f i)
    (hθ' : ∀ σ : LB.Sec L', ∃! a : V, ∀ i, σ.f i = constFn p' _ a * θ'.f i) :
    ∃ b : Vˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * (cst (r ≫ p') z (b : V) * gs r z _ (θ'.f k)) := by
  obtain ⟨τ', hτ'⟩ := sec_pull_down hw hL hL' θ
  obtain ⟨b, hb, -⟩ := hθ' τ'
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * (cst (r ≫ p') z b * gs r z _ (θ'.f k)) :=
    fun Z r z j k hj hk => by rw [hτ' Z r z j k hj hk, hb k, gs_mul _ z _ hk, gs_constFn _ _ _ z hk]
  obtain ⟨s, hs⟩ := thf_secUp hw hL hL' θ'
  obtain ⟨τ, hτ⟩ := exists_sec_along (inv F) (IsIso.inv_hom_id F) s
  obtain ⟨b', hb', -⟩ := hθ τ
  have one : ∀ k, θ'.f k = constFn p' _ (b' * b) * θ'.f k := (sec_eq_iff _ _ _ _).2 fun k y hy => by
    obtain ⟨j, hj⟩ := exists_chart hL (F y)
    have e₁ := hτ _ F y j hj
    have e₂ := key _ (𝟙 _) y j k hj hy
    rw [IsIso.hom_inv_id, hs _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy, hb' j, gs_mul _ y _ hj,
      gs_constFn _ _ _ y hj, hp] at e₁
    rw [Category.id_comp, Category.id_comp] at e₂
    rw [e₂, mul_left_comm, Units.mul_right_inj, ← _root_.mul_assoc, ← H1.cst_mul] at e₁
    exact e₁.symm
  have one' : ∀ k, θ'.f k = constFn p' _ 1 * θ'.f k := (sec_eq_iff _ _ _ _).2 fun k y _ => by
    rw [H1.cst_one, _root_.one_mul]
  have u : b' * b = 1 := (hθ' θ').unique one one'
  exact ⟨⟨b, b', (mul_comm _ _).trans u, u⟩, key⟩

end Calc

section Rig

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem gw_eq_of_rig (hp : Function.Surjective G'.hom.appTop.hom) (L : RigLB G) (L' : RigLB G')
    {F₁ F₂ : G'.left ⟶ G.left} {e₁ e₂ : S' ⟶ S} (hF : F₁ = F₂) (he : e₁ = e₂)
    {w₁ : LB.Iso L'.L (L.L.pull F₁)} {w₂ : LB.Iso L'.L (L.L.pull F₂)} (g₁ : PGen w₁) (g₂ : PGen w₂)
    (m₁ : PMaps w₁ (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig e₁)
    (m₂ : PMaps w₂ (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig e₂)
    {Z : Scheme.{0}} (r : Z ⟶ G'.left) (z : Z) (j : L.L.ι) (k : L'.L.ι) : gw w₁ r z j k = gw w₂ r z j k := by
  subst hF he
  have : w₁ = w₂ := by
    refine gen_eq_of_eq_along_section (fun y => ?_) G'.hom (eSec G') (Over.w η[G']) hp
      ((isGen_iff _).2 g₁) ((isGen_iff _).2 g₂) ?_
    · obtain ⟨i, hi⟩ := exists_chart L'.isLB y
      obtain ⟨j, hj⟩ := exists_chart L.isLB (F₁ y)
      exact ⟨(fun _ => j, i), mem_pull.2 hj, hi⟩
    · rintro s ⟨j, i⟩ ⟨hj, hi⟩
      have k₁ := m₁ _ (𝟙 _) s j (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)
      have k₂ := m₂ _ (𝟙 _) s j (fun _ => i) (fun _ => mem_pull.1 hj) (fun _ => hi)
      rw [Fintype.prod_unique, zpow_one] at k₁ k₂
      have := mul_right_cancel (k₁.symm.trans k₂)
      rw [Category.id_comp] at this
      exact this
  rw [this]

end Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rigIso_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) :
    RigIso m w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  and_congr (isGen_iff w) (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl))

theorem valV_unit (T : CDVR) (b : T.Vˣ) : valV T.V (algebraMap T.V T.Fr (b : T.V)) = 1 := by
  have h₁ : valV T.V (algebraMap T.V T.Fr (b : T.V)) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have h₂ : valV T.V (algebraMap T.V T.Fr ((b⁻¹ : T.Vˣ) : T.V)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have h₃ : valV T.V (algebraMap T.V T.Fr (b : T.V)) * valV T.V (algebraMap T.V T.Fr ((b⁻¹ : T.Vˣ) : T.V)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  exact le_antisymm h₁ (h₃.ge.trans (mul_le_of_le_one_right' h₂))

theorem valV_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (θ : LB.Sec G.PP.L) (θ₂ : LB.Sec G₂.PP.L), ((∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w2 : LB.Iso t.PP.L (G.PP.L.pull m₂.φ)) (σ : LB.Sec t.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ2 : LB.Sec (G.PP.L.pull m₂.φ)), RigIso m₁ w1 ∧ RigIso m₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m₂.φ θ θ2 ∧ ∀ g : t.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m₁.φ → g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))) → ((∀ σ : LB.Sec G₂.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G₂.G.left (le_top : G₂.PP.L.U i ≤ ⊤) ((G₂.G.hom).appTop.hom (toΓ T.V a)) * θ₂.f i) ∧ ∃ (w1 : LB.Iso t₂.PP.L (Xo.univ.t.PP.L.pull n₁.φ)) (w2 : LB.Iso t₂.PP.L (G₂.PP.L.pull n₂.φ)) (σ : LB.Sec t₂.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull n₁.φ)) (θ2 : LB.Sec (G₂.PP.L.pull n₂.φ)), RigIso n₁ w1 ∧ RigIso n₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec n₂.φ θ₂ θ2 ∧ ∀ g : t₂.G.left ⟶ Gx y'.x, g ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = n₁.φ → g ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = t₂.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull n₁.φ).U j ≤ g ⁻¹ᵁ (PPx y'.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y'.s.f (fun _ => j PUnit.unit))) → ∀ a : T.Frˣ, SecBC (RingHom.id T.Fr) (a : T.Fr) y.x y'.x y.s y'.s → valV T.V (a : T.Fr) = 1 := by
  intro E _ _ _ H Dw l Xo c T io
  letI := io.toAlgebra
  intro y y' G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn θ θ₂ ⟨hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, q, hg⟩
    ⟨hθ', w1', w2', σ', s1', θ2', r1', r2', i1', i2', q', hg'⟩ a hab
  obtain ⟨x, hxo, u, htan, heig, hbas, s, hgen⟩ := y
  obtain ⟨x', hxo', u', htan', heig', hbas', s', hgen'⟩ := y'
  dsimp only at hx m₁ n₁ hk hn w1 s1 r1 i1 hg w1' s1' r1' i1' hg' hab
  subst hx
  obtain ⟨g1, p1⟩ := (rigIso_iff _ _).1 r1
  obtain ⟨g2, p2⟩ := (rigIso_iff _ _).1 r2
  obtain ⟨g1', p1'⟩ := (rigIso_iff _ _).1 r1'
  obtain ⟨g2', p2'⟩ := (rigIso_iff _ _).1 r2'
  obtain ⟨wk, gk, pk, -⟩ := (isPullCubical_iff _ _ _).1 k.lin
  obtain ⟨wn, gn, pn, -⟩ := (isPullCubical_iff _ _ _).1 n.lin
  have hsurj : Function.Surjective t.G.hom.appTop.hom :=
    (GlobalTheory.laws_without_cohomology.1 _ t.G ⟨inferInstance, t.semi.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 Xo.univ.proper, t.semi.geomConnected⟩).2

  obtain ⟨wa, Ta⟩ := exists_comp t₂.PP.isLB w1' wk g1' gk Xo.univ.t.PP.isLB t.PP.isLB
  obtain ⟨wb, Tb⟩ := exists_comp t₂.PP.isLB w2' wk g2' gk G₂.PP.isLB t.PP.isLB
  obtain ⟨wc, Tc⟩ := exists_comp G.PP.isLB wn w2 gn g2 G₂.PP.isLB t.PP.isLB
  have ea := @gw_eq_of_rig _ _ _ _ _ _ _ _ hsurj Xo.univ.t.PP t.PP _ _ _ _ hk
    (by rw [k.base, n₁.base, m₁.base]; exact Category.id_comp _) wa w1 (Ta.pgen_comp t₂.PP.isLB g1' gk) g1
    (Ta.pmaps_comp t₂.PP.isLB (fun _ => k.cm.e_comm) p1' pk) p1
  have eb := @gw_eq_of_rig _ _ _ _ _ _ _ _ hsurj G₂.PP t.PP _ _ _ _ hn
    (by rw [k.base, n₂.base, m₂.base, n.base]; exact (Category.comp_id _).trans (Category.id_comp _).symm) wc wb
    (Tc.pgen_comp G.PP.isLB gn g2) (Tb.pgen_comp t₂.PP.isLB g2' gk)
    (Tc.pmaps_comp G.PP.isLB (fun _ => m₂.cm.e_comm) pn p2) (Tb.pmaps_comp t₂.PP.isLB (fun _ => k.cm.e_comm) p2' pk)
  haveI : IsIso n.φ := n.cart.1.isIso_fst_of_isIso
  obtain ⟨b, hb⟩ := exists_unit_of_iso G₂.G.hom G.G.hom (n.cart.1.w.trans (Category.comp_id _)) G₂.PP.isLB G.PP.isLB gn
    θ₂ θ hθ' hθ

  let A := Xo.univ.t.G
  have canon : ∀ (t' : SAB H (Sp T.Fr)) (m : SABMap t' Xo.univ.t x'), ∃ g : t'.G.left ⟶ Gx x',
      g ≫ (snd (Over.mk x') A).left = m.φ ∧ g ≫ (fst (Over.mk x') A).left = t'.G.hom := fun t' m =>
    let a0 : Over.mk (t'.G.hom ≫ x') ⟶ Over.mk x' := Over.homMk t'.G.hom rfl
    let b0 : Over.mk (t'.G.hom ≫ x') ⟶ A := Over.homMk m.φ m.cart.1.w
    ⟨(lift a0 b0).left, congrArg (fun q => q.left) (lift_snd a0 b0), congrArg (fun q => q.left) (lift_fst a0 b0)⟩
  obtain ⟨g, gs₁, gf₁⟩ := canon t m₁
  obtain ⟨g', gs₂, gf₂⟩ := canon t₂ n₁
  have cond : (snd (Over.mk x') A).left ≫ A.hom = (fst (Over.mk x') A).left ≫ x' :=
    (Over.w (snd (Over.mk x') A)).trans (Over.w (fst (Over.mk x') A)).symm
  obtain ⟨h, hφ, hh⟩ : ∃ h : Gx x' ⟶ t.G.left, h ≫ m₁.φ = (snd (Over.mk x') A).left ∧
      h ≫ t.G.hom = (fst (Over.mk x') A).left :=
    ⟨m₁.cart.1.lift _ _ cond, m₁.cart.1.lift_fst _ _ cond, m₁.cart.1.lift_snd _ _ cond⟩
  have ext : ∀ e : Gx x' ⟶ Gx x', e ≫ (snd (Over.mk x') A).left = (snd (Over.mk x') A).left →
      e ≫ (fst (Over.mk x') A).left = (fst (Over.mk x') A).left → e = 𝟙 _ := fun e e₁ e₂ =>
    pullback.hom_ext (e₂.trans (Category.id_comp _).symm) (e₁.trans (Category.id_comp _).symm)
  have kw : k.φ ≫ t₂.G.hom = t.G.hom := k.cart.1.w.trans (Category.comp_id _)
  have hg₁ : h ≫ g = 𝟙 _ := ext _ (by rw [Category.assoc, gs₁, hφ]) (by rw [Category.assoc, gf₁, hh])
  have hg₂ : (h ≫ k.φ) ≫ g' = 𝟙 _ := ext _ (by rw [Category.assoc, gs₂, Category.assoc, hk, hφ])
    (by rw [Category.assoc, gf₂, Category.assoc, kw, hh])
  have le : ∀ (t' : SAB H (Sp T.Fr)) (φ : t'.G.left ⟶ A.left) (g : t'.G.left ⟶ Gx x'),
      g ≫ (snd (Over.mk x') A).left = φ → ∀ j,
      (Xo.univ.t.PP.L.pull φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x').U (fun _ => j) := fun t' φ g e j z hz =>
    Set.mem_iInter.2 fun _ => (congrArg (fun q => q z ∈ Xo.univ.t.PP.L.U j) e).mpr (mem_pull.1 hz)
  have main : ∀ i, s'.f i = scal x' (algebraMap T.V T.Fr (b : T.V)) i * s.f i := by
    intro (i : Fin 1 → Xo.univ.t.PP.L.ι)
    obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
    refine fn_ext fun z hz => ?_
    have hj : m₁.φ (h z) ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (fun q => q z ∈ Xo.univ.t.PP.L.U j) hφ).mpr (Set.mem_iInter.1 hz 0)
    have hj' : n₁.φ (k.φ (h z)) ∈ Xo.univ.t.PP.L.U j := (congrArg (fun q => q (h z) ∈ Xo.univ.t.PP.L.U j) hk).mpr hj
    obtain ⟨κ, hκ⟩ := exists_chart t.PP.isLB (h z)
    obtain ⟨κ', hκ'⟩ := exists_chart t₂.PP.isLB (k.φ (h z))
    obtain ⟨ν, hν⟩ := exists_chart G.PP.isLB (m₂.φ (h z))
    obtain ⟨ν', hν'⟩ := exists_chart G₂.PP.isLB (n.φ (m₂.φ (h z)))
    have hν'' : n₂.φ (k.φ (h z)) ∈ G₂.PP.L.U ν' := (congrArg (fun q => q (h z) ∈ G₂.PP.L.U ν') hn).mp hν'
    have e₁ : gs (𝟙 _) z _ (s.f (fun _ => j)) = (gw w1 h z j κ).val * gs h z _ (σ.f κ) := by
      rw [← isoMaps_pt i1 h z j κ hj hκ, hg g gs₁ gf₁ (fun _ => j) (le t _ g gs₁ j), ← hg₁]
      exact (gs_appLE g _ _ _ h z (mem_pull.2 hj) _).symm
    have e₂ : gs (𝟙 _) z _ (s'.f (fun _ => j)) = (gw w1' (h ≫ k.φ) z j κ').val * gs (h ≫ k.φ) z _ (σ'.f κ') := by
      rw [← isoMaps_pt i1' (h ≫ k.φ) z j κ' hj' hκ', hg' g' gs₂ gf₂ (fun _ => j) (le t₂ _ g' gs₂ j), ← hg₂]
      exact (gs_appLE g' _ _ _ (h ≫ k.φ) z (mem_pull.2 hj') _).symm
    have e₃ := (pullSec_pt q h z ν hν).symm.trans (isoMaps_pt i2 h z ν κ hν hκ)
    have e₄ := (pullSec_pt q' (h ≫ k.φ) z ν' hν'').symm.trans (isoMaps_pt i2' (h ≫ k.φ) z ν' κ' hν'' hκ')
    have e₅ := hb _ (h ≫ m₂.φ) z ν' ν hν' hν
    have e₆ := (Ta _ h z j κ' κ hj' hκ' hκ).symm.trans (ea h z j κ)
    have e₇ := (Tc _ h z ν' ν κ hν' hν hκ).symm.trans ((eb h z ν' κ).trans (Tb _ h z ν' κ' κ hν'' hκ' hκ))
    have c₁ : (h ≫ m₂.φ) ≫ n.φ = (h ≫ k.φ) ≫ n₂.φ := by rw [Category.assoc, hn, Category.assoc]
    have c₂ : cst ((h ≫ m₂.φ) ≫ G.G.hom) z (b : T.V) =
        gs (𝟙 _) z _ (scal x' (algebraMap T.V T.Fr (b : T.V)) (fun _ => j)) := by
      rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, hh, cst_comp]
      exact ((gs_constFn (fst (Over.mk x') A).left _ (𝟙 _) z hz _).trans (by rw [Category.id_comp])).symm
    rw [c₁, e₄, e₃, c₂, mul_left_comm, ← _root_.mul_assoc (gw wn _ _ _ _).val, ← Units.val_mul, e₇,
      Units.val_mul, _root_.mul_assoc, mul_left_comm _ (gw w2' _ _ _ _).val, Units.mul_right_inj] at e₅
    rw [gs_mul _ z _ hz, e₁, e₂, e₅, ← e₆, Units.val_mul]
    ring
  obtain ⟨pm, h₁, h₂, h₃⟩ := hab
  obtain rfl : pm = 𝟙 _ := ext pm h₁ (h₂.trans ((congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)))
  have main' : ∀ i, s'.f i = scal x' (a : T.Fr) i * s.f i := fun i => fn_ext fun z hz => by
    rw [← h₃ i le_rfl]
    exact (gs_appLE (𝟙 _) _ _ _ (𝟙 _) z hz _).trans (by rw [Category.id_comp])
  rw [(hgen s').unique main' main]
  exact valV_unit T b

end GlobalTheory.IntegralGenerator
