import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GenericPoints
open GlobalTheory.FieldBaseChange GlobalTheory.Points GlobalTheory.TuplePoint

section Clear
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

abbrev resGen (G : Over (Sp R)) (L : LB G.left) (k : ℕ) :
    SecOver G.hom (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))) →ₛₗ[algebraMap R K]
      SecOver (pullback.snd G.hom (spMap (algebraMap R K)))
        (LB.LinComb L (K := Fin 1) (fun _ => pullback.fst G.hom (spMap (algebraMap R K))) (fun _ => (k : ℤ))) :=
  pullOver L _ pullback.condition (fun _ => (Category.comp_id _).symm)

theorem exists_clear {I : Ideal R} {D : Out.DegData R I} {A : Out.PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (U : Out.Unif I D A G) (k : ℕ) (hk : 1 ≤ k)
    (s : SecOver (pullback.snd G.hom (spMap (algebraMap R K)))
        (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (spMap (algebraMap R K))) (fun _ => (k : ℤ)))) :
    ∃ (r : R) (σ : Out.H0 U.LG.L k), r ≠ 0 ∧ resGen G U.LG.L k σ = algebraMap R K r • s := by
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  have e₁ : spMap e.symm.toRingEquiv.toRingHom ≫ spMap (algebraMap R K) = Out.jK R := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact e.symm.commutes x
  have e₂ : spMap e.toRingEquiv.toRingHom ≫ Out.jK R = spMap (algebraMap R K) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact e.commutes x
  have e₃ : spMap e.toRingEquiv.toRingHom ≫ spMap e.symm.toRingEquiv.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact e.apply_symm_apply x
  let h : pullback G.hom (Out.jK R) ⟶ pullback G.hom (spMap (algebraMap R K)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap e.symm.toRingEquiv.toRingHom)
      (by rw [Category.assoc, e₁, pullback.condition])
  let h' : pullback G.hom (spMap (algebraMap R K)) ⟶ pullback G.hom (Out.jK R) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap e.toRingEquiv.toRingHom)
      (by rw [Category.assoc, e₂, pullback.condition])
  have a₁ : h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have a₂ : h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap e.symm.toRingEquiv.toRingHom := pullback.lift_snd _ _ _
  have b₁ : h' ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have b₂ : h' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap e.toRingEquiv.toRingHom := pullback.lift_snd _ _ _
  have hh : h' ≫ h = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, a₁, b₁, Category.id_comp]
    · rw [Category.assoc, a₂, reassoc_of% b₂, e₃, Category.id_comp, Category.comp_id]
  let s' := pullOver U.LG.L (fun _ : Fin 1 => (k : ℤ)) a₂ (φ' := fun _ => pullback.fst G.hom (Out.jK R))
    (fun _ => a₁.symm) s
  obtain ⟨F, ⟨r, hr, σ, f, H, -⟩, -⟩ := (U.expand k hk).1 s'
  refine ⟨r, σ, hr, ?_⟩
  have H' := (secScal_iff (π := G.hom) (pullback.condition (f := G.hom) (g := Out.jK R))
    (fun _ => (Category.comp_id _).symm) U.LG.isLB s' σ _ (algebraMap R (FractionRing R)) rfl r).1 H
  have H'' := congrArg (pullOver U.LG.L (fun _ : Fin 1 => (k : ℤ)) b₂
    (φ' := fun _ => pullback.fst G.hom (spMap (algebraMap R K))) (fun _ => b₁.symm)) H'
  rw [map_smulₛₗ] at H''
  refine Eq.trans ?_ (H''.trans ?_)
  · refine sec_ext' U.LG.isLB fun y J hJ => ?_
    refine (sval_pullOver _ _ _ _ hJ).trans (Eq.trans ?_
      ((sval_pullOver _ _ _ _ hJ).trans (sval_pullOver _ _ _ _ hJ)).symm)
    rw [Category.assoc, b₁]
  · refine congrArg₂ (· • ·) (e.commutes r) (sec_ext' U.LG.isLB fun y J hJ => ?_)
    refine ((sval_pullOver _ _ _ _ hJ).trans (sval_pullOver _ _ _ _ hJ)).trans ?_
    rw [Category.assoc, hh, Category.comp_id]

end Clear

section Frame
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] {Y Z : Scheme.{0}} {L : LB Z}

theorem exists_chart_loc (hL : L.IsLB) (x : Sp R ⟶ Z) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := exists_chart hL (x (cpt R))
  exact ⟨j, (top_le_iff_cpt x _).2 hj⟩

theorem valR_cocycle (hL : L.IsLB) (x : Sp R ⟶ Z) {i j k : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) : valR x (L.U i ⊓ L.U j) (L.g i j).val * valR x (L.U j ⊓ L.U k) (L.g j k).val =
      valR x (L.U i ⊓ L.U k) (L.g i k).val := by
  apply toStkA_injective
  rw [map_mul, toStkA_valR x (L.U i ⊓ L.U j) _ (fun _ hz => ⟨hi hz, hj hz⟩),
    toStkA_valR x (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩),
    toStkA_valR x (L.U i ⊓ L.U k) _ (fun _ hz => ⟨hi hz, hk hz⟩), ← Units.val_mul,
    gm_cocycle hL x _ (hi trivial) (hj trivial) (hk trivial)]

theorem exists_genFrm (hL : L.IsLB) (ρ : R →+* K) (x : Sp R ⟶ Z) (τ : L.ι → R) (hτ : IsFrm L x τ) :
    ∃ τ' : L.ι → K, IsFrm L (spMap ρ ≫ x) τ' ∧ ∀ j, ⊤ ≤ x ⁻¹ᵁ L.U j → τ' j = ρ (τ j) := by
  obtain ⟨j₀, h₀⟩ := exists_chart_loc hL x
  have h₀' := FormalValue.top_le_comp h₀ (spMap ρ)
  refine ⟨fun j => valR (spMap ρ ≫ x) (L.U j ⊓ L.U j₀) (L.g j j₀).val * ρ (τ j₀), ⟨fun j hj => ?_, fun j j' hj => ?_⟩,
    fun j hj => ?_⟩
  · exact (FormalValue.isUnit_valR _ (L.U j ⊓ L.U j₀) (fun _ hz => ⟨hj hz, h₀' hz⟩) _).mul ((hτ.1 j₀ h₀).map ρ)
  · beta_reduce
    rw [← _root_.mul_assoc, valR_cocycle hL _ (fun _ hz => (hj hz).1) (fun _ hz => (hj hz).2) h₀']
  · have hh : ⊤ ≤ x ⁻¹ᵁ (L.U j ⊓ L.U j₀) := fun _ hz => ⟨hj hz, h₀ hz⟩
    beta_reduce
    rw [hτ.2 j j₀ hh, map_mul, valR_spMap_comp ρ x _ hh]

theorem le_wchart {p : Y ⟶ Z} {A : Type} [CommRing A] {y : Sp A ⟶ Y} {j : L.ι} (hj : ⊤ ≤ (y ≫ p) ⁻¹ᵁ L.U j) :
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hj hz

theorem sval_trans' {p : Y ⟶ Z} {m : ℕ} (s : SecP L p m) (y : Sp R ⟶ Y) {i j : L.ι} (hi : ⊤ ≤ (y ≫ p) ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ (y ≫ p) ⁻¹ᵁ L.U j) :
    ArcPts.sval s y i = valR (y ≫ p) (L.U i ⊓ L.U j) (L.g i j).val ^ m * ArcPts.sval s y j := by
  apply toStkA_injective
  have e := sec_trans s y (cpt R) (j := fun _ => i) (j' := fun _ => j) (le_wchart hi trivial) (le_wchart hj trivial)
  rw [map_mul, map_pow, toStkA_valR (y ≫ p) (L.U i ⊓ L.U j) _ (fun _ hz => ⟨hi hz, hj hz⟩)]
  refine (FormalValue.toStkA_valR_eq_gs y _ _ (le_wchart hi) _).trans (e.trans (congrArg₂ (· * ·) ?_
    (FormalValue.toStkA_valR_eq_gs y _ _ (le_wchart hj) _).symm))
  simp [Geo.Tor.trF]

theorem hasVal_of_chart {p : Y ⟶ Z} {m : ℕ} (s : SecP L p m) (y : Sp R ⟶ Y) {τ : L.ι → R} (hτ : IsFrm L (y ≫ p) τ)
    {r : R} {j : L.ι} (hj : ⊤ ≤ (y ≫ p) ⁻¹ᵁ L.U j) (h : ArcPts.sval s y j = r * τ j ^ m) : HasVal s y τ r := by
  intro i hi
  rw [sval_trans' s y hi hj, h, hτ.2 i j (fun _ hz => ⟨hi hz, hj hz⟩)]
  ring

theorem valR_gen_trans (e : Y ⟶ Z) (t : LB.Gen (L.pull e)) (ht : t.IsGen) (y : Sp K ⟶ Y) (i j : L.ι)
    (hi : ⊤ ≤ (y ≫ e) ⁻¹ᵁ L.U i) (hj : ⊤ ≤ (y ≫ e) ⁻¹ᵁ L.U j) :
    valR y _ (t.s fun _ => i).val = valR (y ≫ e) _ (L.g i j).val * valR y _ (t.s fun _ => j).val := by
  have h : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L (K := PUnit) (fun _ => e) (fun _ => i) ⊓
      LB.wchart L (K := PUnit) (fun _ => e) (fun _ => j)) :=
    fun z hz => ⟨Set.mem_iInter.2 fun _ => hi hz, Set.mem_iInter.2 fun _ => hj hz⟩
  have e1 := congrArg (fun u => valR y _ u.val) (ht (fun _ => i) (fun _ => j))
  refine (valR_res_unit y inf_le_left h _).symm.trans (e1.trans ((valR_mul_unit y h _ _).trans ?_))
  exact congrArg₂ (· * ·) ((valR_linComb_g y L e 1 _ _ h).trans (zpow_one _)) (valR_res_unit y inf_le_right h _)

omit [IsLocalRing R] in
theorem sval_smul {p : Y ⟶ Z} {m : ℕ} (π : Y ⟶ Sp R) (c : R)
    (s : SecOver π (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (m : ℤ)))) (y : Sp R ⟶ Y) (hy : y ≫ π = 𝟙 _)
    {j : L.ι} (hj : ⊤ ≤ (y ≫ p) ⁻¹ᵁ L.U j) :
    ArcPts.sval (L := L) (p := p) (m := m) (c • s : SecOver π _) y j = c * ArcPts.sval (L := L) (p := p) (m := m) s y j := by
  refine (valR_mul y _ (le_wchart hj) (Out.resTop _ (Out.scal π c)) _).trans (congrArg (· * _) ?_)
  refine (valR_res y le_top (le_wchart hj) _).trans ((valR_comp y π ⊤ _).symm.trans ?_)
  rw [hy, ← Spec.map_id]
  exact valR_specMap (A := CommRingCat.of R) (𝟙 _) c

omit [IsLocalRing R] in
theorem hasVal_smul {p : Y ⟶ Z} {m : ℕ} (π : Y ⟶ Sp R) (c : R)
    (s : SecOver π (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (m : ℤ)))) (y : Sp R ⟶ Y) (hy : y ≫ π = 𝟙 _)
    {τ : L.ι → R} {r : R} (h : HasVal (L := L) (p := p) (m := m) s y τ r) :
    HasVal (L := L) (p := p) (m := m) (c • s : SecOver π _) y τ (c * r) := fun j hj => by
  rw [sval_smul π c s y hy hj, h j hj, _root_.mul_assoc]

end Frame

section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]

theorem sval_resGen {R K : Type} [CommRing R] [Field K] [Algebra R K] (G : Over (Sp R)) (L : LB G.left) (k : ℕ)
    (σ : Out.H0 L k) (x : Sp R ⟶ G.left) (y : Sp K ⟶ pullback G.hom (spMap (algebraMap R K)))
    (hy : y ≫ pullback.fst _ _ = spMap (algebraMap R K) ≫ x) {j : L.ι} (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    ArcPts.sval (L := L) (p := pullback.fst G.hom (spMap (algebraMap R K))) (m := k) (resGen G L k σ) y j =
      algebraMap R K (valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)) (σ.f (fun _ => j))) := by
  have hj' : ⊤ ≤ (y ≫ pullback.fst G.hom (spMap (algebraMap R K))) ⁻¹ᵁ L.U j := by
    rw [hy]; exact FormalValue.top_le_comp hj _
  refine (valR_res y (wchart_eq (φ := fun _ : Fin 1 => 𝟙 G.left) (fun _ => (Category.comp_id _).symm) _).le
    (le_wchart hj') _).trans ((valR_comp y _ _ _).symm.trans ?_)
  rw [hy]
  exact valR_spMap_comp _ x _ (le_wchart (p := 𝟙 G.left) hj) _

def ValsAt {V : Type} {Z : Scheme.{0}} {L : LB Z} (x : V → (Sp ℂ⟦X⟧ ⟶ Z)) (τ : V → L.ι → ℂ⟦X⟧) {j : ℕ}
    (σ : Out.H0 L j) (f : V → ℂ⸨X⸩) : Prop :=
  ∀ v jL, ⊤ ≤ x v ⁻¹ᵁ L.U jL →
    (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) (valR (x v) (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => jL)) (σ.f (fun _ => jL))) =
      f v * (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) (τ v jL) ^ j

theorem exists_genPts (A : AnArc (𝓞 E)) (t : SAB H (Sp ℂ⟦X⟧)) (L : RigLB t.G) (hb : L = t.PP)
    (x : A.V → (Over.mk (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ⟶ t.G)) (τ : A.V → L.L.ι → ℂ⟦X⟧)
    (add : ∀ v v', x (v + v') = x v * x v') (lin : ∀ (e : 𝓞 E) v, x (A.actV e v) = x v ≫ t.act.act e)
    (frm : ∀ v, IsFrm L.L (x v).left (τ v))
    (rig : ∀ j, ⊤ ≤ (x 0).left ⁻¹ᵁ L.L.U j →
      τ 0 j = valR (𝟙 (Sp ℂ⟦X⟧)) ((L.L.pull (eSec t.G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val)
    (sig : ∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∃ (m : ℕ) (σ : Out.H0 L.L j),
      ValsAt (fun v => (x v).left) τ σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th v))
    (span : ∀ (j : ℕ) [NeZero j] (σ : Out.H0 L.L j), ∃ f, IsComb A j Set.univ f ∧
      ValsAt (fun v => (x v).left) τ σ f ∧ ((∀ v, f v = 0) → ∀ i, σ.f i = 0))
    (clear : ∀ k : ℕ, 1 ≤ k → ∀ s, ∃ (r : ℂ⟦X⟧) (σ : Out.H0 L.L k), r ≠ 0 ∧
      resGen (K := ℂ⸨X⸩) t.G L.L k σ = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r • s) :
    ∃ Φ : GenPts A t (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)), ∀ v,
      (Φ.x v).left = spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) ≫ (x v).left ∧ ∀ (jL : L.L.ι) (j : t.PP.L.ι), HEq jL j →
        ⊤ ≤ (x v).left ⁻¹ᵁ L.L.U jL → Φ.τ v j = (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) (τ v jL) := by
  subst hb
  have hL := t.PP.isLB
  have hid : spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = 𝟙 _ := Spec.map_id _
  let q : Over.mk (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) ⟶ Over.mk (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) :=
    Over.homMk (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) (by
      show _ ≫ spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = _
      rw [hid]; exact Category.comp_id _)
  choose τ' hτ' eτ' using fun v => exists_genFrm hL (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) (x v).left (τ v) (frm v)
  have f₁ : ∀ v, fib (q ≫ x v) ≫ pullback.fst _ _ = spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) ≫ (x v).left :=
    fun v => pullback.lift_fst _ _ _
  have f₂ : ∀ v, fib (q ≫ x v) ≫ pullback.snd _ _ = 𝟙 _ := fun v => pullback.lift_snd _ _ _
  have key : ∀ {j : ℕ} (σ : Out.H0 t.PP.L j) (f : A.V → ℂ⸨X⸩), ValsAt (fun v => (x v).left) τ σ f → ∀ v,
      HasVal (L := t.PP.L) (p := pullback.fst t.G.hom (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩))) (m := j)
        (resGen t.G t.PP.L j σ) (fib (q ≫ x v)) (τ' v) (f v) := fun σ f h v => by
    obtain ⟨j₀, h₀⟩ := exists_chart_loc hL (x v).left
    refine hasVal_of_chart _ _ (by rw [f₁]; exact hτ' v) (j := j₀)
      (by rw [f₁]; exact FormalValue.top_le_comp h₀ _) ?_
    rw [sval_resGen t.G t.PP.L _ σ (x v).left _ (f₁ v) h₀, eτ' v j₀ h₀]
    exact h v j₀ h₀
  have hsig : ∀ (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ),
      ∃ s : SecP t.PP.L (pullback.fst t.G.hom (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩))) j, ∀ [NeZero j], th ∈ A.Theta j α →
        ∀ v, HasVal s (fib (q ≫ x v)) (τ' v) (A.FSum j α th v) := fun j α th => by
    by_cases h : NeZero j ∧ th ∈ A.Theta j α
    · have := h.1
      obtain ⟨m, σ, hσ⟩ := sig j α th h.2
      refine ⟨(HahnSeries.single (-m : ℤ) (1 : ℂ) : ℂ⸨X⸩) • resGen t.G t.PP.L j σ, fun _ v => ?_⟩
      have e := hasVal_smul _ (HahnSeries.single (-m : ℤ) (1 : ℂ) : ℂ⸨X⸩) _ _ (f₂ v) (key σ _ hσ v)
      rwa [← _root_.mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, _root_.mul_one, HahnSeries.single_zero_one,
        _root_.one_mul] at e
    · exact ⟨DVR.SecOps.secZero, fun hth => absurd ⟨inferInstance, hth⟩ h⟩
  choose sg hsg using hsig
  have hcl : ∀ (j : ℕ) [NeZero j] (s : SecOver (pullback.snd t.G.hom (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)))
      (LB.LinComb t.PP.L (K := Fin 1) (fun _ => pullback.fst t.G.hom (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)))
        (fun _ => (j : ℤ)))), ∃ (c : ℂ⸨X⸩) (σ : Out.H0 t.PP.L j), c ≠ 0 ∧ s = c • resGen t.G t.PP.L j σ :=
    fun j _ s => by
      obtain ⟨r, σ, hr, e⟩ := clear j NeZero.one_le s
      have hr' : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r ≠ 0 := fun h => hr (IsFractionRing.injective ℂ⟦X⟧ ℂ⸨X⸩ (h.trans (map_zero _).symm))
      exact ⟨(algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)⁻¹, σ, inv_ne_zero hr', by rw [e, inv_smul_smul₀ hr']⟩
  refine ⟨{ x := fun v => q ≫ x v
            add := fun v v' => by rw [add, MonObj.comp_mul]
            lin := fun e v => by rw [lin, Category.assoc]
            τ := τ'
            frm := hτ'
            rig := fun j hj => ?_
            sig := sg
            val := fun j _ α th hth v => hsg j α th hth v
            span := fun j _ s => ?_
            sep := fun j _ s hs i => ?_ }, fun v => ⟨rfl, fun jL j h hj => ?_⟩⟩
  · have h0 : x 0 = 1 := by
      have := add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    have h1 : (x 0).left = eSec t.G := by
      rw [h0]
      show spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ≫ eSec t.G = _
      rw [hid]; exact Category.id_comp _
    obtain ⟨j₀, h₀⟩ := exists_chart_loc hL (x 0).left
    have h₀' := FormalValue.top_le_comp h₀ (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩))
    have hj' : ⊤ ≤ (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) ≫ (x 0).left) ⁻¹ᵁ t.PP.L.U j := hj
    rw [(hτ' 0).2 j j₀ (fun _ hz => ⟨hj' hz, h₀' hz⟩), eτ' 0 j₀ h₀, rig j₀ h₀]
    rw [h1] at hj' h₀' h₀
    refine Eq.trans ?_ (valR_gen_trans (eSec t.G) t.PP.rig t.PP.rigGen (spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) j j₀ hj' h₀').symm
    refine congrArg₂ (· * ·) (by rw [h1]) ?_
    refine (valR_spMap_comp _ (𝟙 (Sp ℂ⟦X⟧)) ((t.PP.L.pull (eSec t.G)).U (fun _ => j₀))
      (fun _ hz => Set.mem_iInter.2 fun _ => h₀ hz) _).symm.trans ?_
    rw [Category.comp_id]
  · obtain ⟨c, σ, -, rfl⟩ := hcl j s
    obtain ⟨f, ⟨n, r, α, th, h₁, h₂⟩, hf, -⟩ := span j σ
    refine ⟨fun v => c * f v, ⟨n, fun i => c * r i, α, th, fun i => ⟨trivial, (h₁ i).2⟩, fun v => ?_⟩,
      fun v => hasVal_smul _ c _ _ (f₂ v) (key σ f hf v)⟩
    simp only [h₂, Finset.mul_sum, _root_.mul_assoc]
  · obtain ⟨c, σ, hc, rfl⟩ := hcl j s
    obtain ⟨f, -, hf, hz⟩ := span j σ
    have hσ : (show SecOver t.G.hom _ from σ) = 0 := DVR.SecOps.sec_ext (hz fun v => by
      obtain ⟨j₀, h₀⟩ := exists_chart_loc hL (fib (q ≫ x v) ≫ pullback.fst _ _)
      have e := (hasVal_smul _ c _ _ (f₂ v) (key σ f hf v) j₀ h₀).symm.trans (hs v j₀ h₀)
      rw [f₁] at h₀
      rw [zero_mul, mul_eq_zero, mul_eq_zero] at e
      exact (e.resolve_right (((hτ' v).1 j₀ h₀).pow j).ne_zero).resolve_left hc)
    have e : c • resGen (K := ℂ⸨X⸩) t.G t.PP.L j σ = 0 := by
      rw [show resGen (K := ℂ⸨X⸩) t.G t.PP.L j σ = 0 from (congrArg _ hσ).trans (map_zero _), smul_zero]
    exact congrArg (fun s => LB.Sec.f s i) e
  · obtain rfl := eq_of_heq h
    exact eτ' v jL hj

end Main

end GlobalTheory.GenericPoints
