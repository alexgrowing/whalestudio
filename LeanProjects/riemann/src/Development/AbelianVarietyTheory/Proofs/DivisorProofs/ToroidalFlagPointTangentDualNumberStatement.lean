import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigLetters

section Alg

variable {Gp Ω R Ix : Type} [CommGroup Gp] [Field Ω] [CommRing R] [Fintype Ix] [DecidableEq Ix]

private theorem isUnit_chars (b : Module.Basis Ix ℤ R) (χ : Ix → R →+* Ω) (hχ : Function.Injective χ) :
    IsUnit (Matrix.of fun τ j => χ τ (b j)) := by
  rw [← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
  intro g hg
  have hli := (linearIndependent_monoidHom R Ω).comp (fun τ => (χ τ : R →* Ω))
    (fun σ τ h => hχ (RingHom.coe_monoidHom_injective h))
  rw [Fintype.linearIndependent_iff] at hli
  apply hli g
  funext r
  have hb : ∀ j, ∑ τ, g τ * χ τ (b j) = 0 := fun j => by
    simpa [Finset.sum_apply, Matrix.row] using congrFun hg j
  have : ∑ τ, g τ * χ τ r = 0 := by
    rw [← b.sum_repr r]
    simp only [map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun j _ => by rw [← Finset.smul_sum, hb, smul_zero]
  simpa [Finset.sum_apply] using this

variable (sm : Ω → Gp →* Gp) (ρ : R → Gp →* Gp)

private theorem sm_sum (sm_add : ∀ v, sm 0 v = 1 → ∀ a a', sm (a + a') v = sm a v * sm a' v)
    {κ : Type} (s : Finset κ) (f : κ → Ω) (v : Gp) (hv : sm 0 v = 1) :
    sm (∑ i ∈ s, f i) v = ∏ i ∈ s, sm (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, sm_add v hv, ih]

private theorem exists_projectors (b : Module.Basis Ix ℤ R) (χ : Ix → R →+* Ω) (hχ : Function.Injective χ)
    (sm_sm : ∀ a a' v, sm a (sm a' v) = sm (a * a') v) (sm_one : ∀ v, sm 1 v = v)
    (sm_add : ∀ v, sm 0 v = 1 → ∀ a a', sm (a + a') v = sm a v * sm a' v)
    (ρ_sm : ∀ r a v, ρ r (sm a v) = sm a (ρ r v)) (ρ_one : ∀ v, ρ 1 v = v)
    (ρ_mul : ∀ r s v, ρ (r * s) v = ρ s (ρ r v)) (ρ_add : ∀ r s v, ρ (r + s) v = ρ r v * ρ s v) :
    ∃ P : Ix → Gp →* Gp,
      (∀ σ τ v, sm 0 v = 1 → (∀ r, ρ r v = sm (χ τ r) v) → P σ v = if τ = σ then v else 1) ∧
      ∀ v, sm 0 v = 1 → ∏ σ, P σ v = v ∧ ∀ σ, sm 0 (P σ v) = 1 ∧ ∀ r, ρ r (P σ v) = sm (χ σ r) (P σ v) := by
  obtain ⟨A, hA⟩ := isUnit_chars b χ hχ
  obtain ⟨B, hAB, hBA⟩ : ∃ B : Matrix Ix Ix Ω, (∀ τ σ, ∑ j, B j σ * χ τ (b j) = if τ = σ then 1 else 0) ∧
      ∀ j k, ∑ τ, χ τ (b k) * B j τ = if j = k then 1 else 0 := by
    refine ⟨(A⁻¹ : (Matrix Ix Ix Ω)ˣ), fun τ σ => ?_, fun j k => ?_⟩
    · have := congrFun (congrFun A.mul_inv τ) σ
      rw [Matrix.mul_apply, hA, Matrix.one_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
    · have := congrFun (congrFun A.inv_mul j) k
      rw [Matrix.mul_apply, hA, Matrix.one_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => _root_.mul_comm _ _
  have hite : ∀ (p : Prop) [Decidable p] (v : Gp), sm 0 v = 1 → sm (if p then 1 else 0) v = if p then v else 1 := by
    intro p _ v hv
    split_ifs
    · exact sm_one v
    · exact hv
  have hρ0 : ∀ r v, sm 0 v = 1 → sm 0 (ρ r v) = 1 := fun r v hv => by rw [← ρ_sm, hv, map_one]
  let P : Ix → Gp →* Gp := fun σ => ∏ j, (sm (B j σ)).comp (ρ (b j))
  have hP : ∀ σ v, P σ v = ∏ j, sm (B j σ) (ρ (b j) v) := fun σ v => by
    simp only [P, MonoidHom.finsetProd_apply, MonoidHom.comp_apply]
  refine ⟨P, fun σ τ v hv he => ?_, fun v hv => ?_⟩
  · rw [hP, ← hite _ v hv, ← hAB, sm_sum sm sm_add _ _ v hv]
    exact Finset.prod_congr rfl fun j _ => by rw [he, sm_sm]
  · have hP0 : ∀ σ, sm 0 (P σ v) = 1 := fun σ => by
      rw [hP, map_prod]
      exact Finset.prod_eq_one fun j _ => by rw [sm_sm, zero_mul, hρ0 _ v hv]
    have key : ∀ r, ρ r v = ∏ τ, sm (χ τ r) (P τ v) := by
      let f : R →+ Additive Gp := AddMonoidHom.mk' (fun r => Additive.ofMul (ρ r v))
        (fun r s => by rw [ρ_add, ofMul_mul])
      let g : R →+ Additive Gp := AddMonoidHom.mk' (fun r => Additive.ofMul (∏ τ, sm (χ τ r) (P τ v)))
        (fun r s => by
          rw [← ofMul_mul, ← Finset.prod_mul_distrib]
          congr 1
          exact Finset.prod_congr rfl fun τ _ => by rw [map_add, sm_add _ (hP0 τ)])
      have hfg : f.toIntLinearMap = g.toIntLinearMap := b.ext fun k => by
        show Additive.ofMul (ρ (b k) v) = Additive.ofMul (∏ τ, sm (χ τ (b k)) (P τ v))
        congr 1
        simp only [hP, map_prod, sm_sm]
        rw [Finset.prod_comm]
        have : ∀ j, ∏ τ, sm (χ τ (b k) * B j τ) (ρ (b j) v) = if j = k then ρ (b j) v else 1 := fun j => by
          rw [← sm_sum sm sm_add _ _ _ (hρ0 _ v hv), hBA, hite _ _ (hρ0 _ v hv)]
        simp only [this, Finset.prod_ite_eq', Finset.mem_univ, if_true]
      intro r
      exact Additive.ofMul.injective (LinearMap.congr_fun hfg r)
    refine ⟨?_, fun σ => ⟨hP0 σ, fun r => ?_⟩⟩
    · simpa only [map_one, sm_one, ρ_one] using (key 1).symm
    · have h1 : ρ r (P σ v) = ∏ j, ∏ τ, sm (χ τ r * (B j σ * χ τ (b j))) (P τ v) := by
        rw [hP σ, map_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [ρ_sm, ← ρ_mul, key, map_prod]
        refine Finset.prod_congr rfl fun τ _ => ?_
        rw [sm_sm, map_mul]
        congr 2
        ring
      rw [h1, Finset.prod_comm]
      have : ∀ τ, ∏ j, sm (χ τ r * (B j σ * χ τ (b j))) (P τ v) =
          if τ = σ then sm (χ τ r) (P τ v) else 1 := fun τ => by
        rw [← sm_sum sm sm_add _ _ _ (hP0 τ), ← Finset.mul_sum, hAB, ← sm_sm, hite _ _ (hP0 τ)]
        split_ifs
        · rfl
        · exact map_one _
      simp only [this, Finset.prod_ite_eq', Finset.mem_univ, if_true]

private theorem unique_coords (b : Module.Basis Ix ℤ R) (χ : Ix → R →+* Ω) (hχ : Function.Injective χ)
    (sm_sm : ∀ a a' v, sm a (sm a' v) = sm (a * a') v) (sm_one : ∀ v, sm 1 v = v)
    (sm_add : ∀ v, sm 0 v = 1 → ∀ a a', sm (a + a') v = sm a v * sm a' v)
    (ρ_sm : ∀ r a v, ρ r (sm a v) = sm a (ρ r v)) (ρ_one : ∀ v, ρ 1 v = v)
    (ρ_mul : ∀ r s v, ρ (r * s) v = ρ s (ρ r v)) (ρ_add : ∀ r s v, ρ (r + s) v = ρ r v * ρ s v)
    {m : Ix → ℕ} (U : ∀ τ, Fin (m τ) → Gp) (U0 : ∀ τ i, sm 0 (U τ i) = 1)
    (UE : ∀ τ i r, ρ r (U τ i) = sm (χ τ r) (U τ i))
    (UB : ∀ τ v, sm 0 v = 1 → (∀ r, ρ r v = sm (χ τ r) v) → ∃! a : Fin (m τ) → Ω, ∏ i, sm (a i) (U τ i) = v)
    {n : ℕ} (e : Fin n ≃ Σ τ, Fin (m τ)) (v : Gp) (hv : sm 0 v = 1) :
    ∃! a : Fin n → Ω, ∏ k, sm (a k) (U (e k).1 (e k).2) = v := by
  obtain ⟨P, hP1, hP2⟩ := exists_projectors sm ρ b χ hχ sm_sm sm_one sm_add ρ_sm ρ_one ρ_mul ρ_add
  obtain ⟨hs, hP⟩ := hP2 v hv
  have hre : ∀ a : Fin n → Ω, ∏ k, sm (a k) (U (e k).1 (e k).2) =
      ∏ τ, ∏ i, sm (a (e.symm ⟨τ, i⟩)) (U τ i) := fun a => by
    rw [← Fintype.prod_sigma' (fun τ i => sm (a (e.symm ⟨τ, i⟩)) (U τ i))]
    exact Fintype.prod_equiv e _ _ fun k => by simp
  have hc : ∀ a : Fin n → Ω, ∏ k, sm (a k) (U (e k).1 (e k).2) = v ↔
      ∀ σ, ∏ i, sm (a (e.symm ⟨σ, i⟩)) (U σ i) = P σ v := fun a => by
    rw [hre]
    refine ⟨fun h σ => ?_, fun h => by rw [← hs]; exact Finset.prod_congr rfl fun σ _ => h σ⟩
    rw [← h, map_prod]
    have : ∀ τ, P σ (∏ i, sm (a (e.symm ⟨τ, i⟩)) (U τ i)) =
        if τ = σ then ∏ i, sm (a (e.symm ⟨τ, i⟩)) (U τ i) else 1 := fun τ => by
      apply hP1
      · rw [map_prod]
        exact Finset.prod_eq_one fun i _ => by rw [sm_sm, zero_mul, U0]
      · intro r
        rw [map_prod, map_prod]
        exact Finset.prod_congr rfl fun i _ => by rw [ρ_sm, UE, sm_sm, sm_sm, _root_.mul_comm]
    simp only [this, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  choose g hg hu using fun σ => UB σ (P σ v) (hP σ).1 (hP σ).2
  refine ⟨fun k => g (e k).1 (e k).2, (hc _).2 fun σ => ?_, fun a ha => funext fun k => ?_⟩
  · rw [← hg σ]
    exact Finset.prod_congr rfl fun i _ => by rw [Equiv.apply_symm_apply]
  · have := congrFun (hu (e k).1 _ ((hc a).1 ha (e k).1)) (e k).2
    simpa using this

end Alg

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)

private theorem letters_nodup : (letters Dw).Nodup := by
  unfold letters
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => (List.nodup_finRange _).map (fun i j h => ?_), ?_⟩
  · simpa using h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hxa hxb
    simp only [List.mem_map, List.mem_finRange, true_and] at hxa hxb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, hj⟩ := hxb
    have := congrArg Sigma.fst hj
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective this.symm)

private theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  unfold letters
  refine List.mem_flatMap.2 ⟨Fintype.equivFin (E →+* ℂ) τ, List.mem_finRange _, ?_⟩
  generalize hσ : (Fintype.equivFin (E →+* ℂ)).symm (Fintype.equivFin (E →+* ℂ) τ) = σ
  obtain rfl : σ = τ := by rw [← hσ, Equiv.symm_apply_apply]
  exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩

end Letters

end GlobalTheory.EigLetters

open GlobalTheory.EigLetters in

theorem _root_.GlobalTheory.T.toroidal_flag_point_tangent_dual_number : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {Ω : Type} [Field Ω] (y : GlobalTheory.ShFam.Pad.FlagPt Z Ω) (w : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber Ω) ⟶ Z.t.G.left), Formalism.L2.Pj.IsTanAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) w → ∃! a : Fin (GlobalTheory.ShFam.Pad.letters Dw).length → Ω, Formalism.L2.Pj.IsCombAtG Z.t (y.y ≫ GlobalTheory.Toroidal.genι Z) (fun k => y.u ((GlobalTheory.ShFam.Pad.letters Dw).get k).1 ((GlobalTheory.ShFam.Pad.letters Dw).get k).2) a w := by
  intro E _ _ _ H Dw l Xo c O _ β Z Ω _ y w hw
  classical
  let x0 := y.y ≫ GlobalTheory.Toroidal.genι Z
  let e : Fin (letters Dw).length ≃ Letter Dw := (letters_nodup Dw).getEquivOfForallMemList _ (mem_letters Dw)
  let χ : (E →+* ℂ) → 𝓞 E →+* Ω := fun τ => (y.fK.comp (embF c τ)).comp (algebraMap (𝓞 E) E)
  have hχ : Function.Injective χ := fun σ τ h => by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    refine RingHom.ext fun a => ?_
    exact congrArg Subtype.val (y.fK.injective (RingHom.congr_fun h a))
  let ρ : 𝓞 E → (tEpsG x0 ⟶ Z.t.G) →* (tEpsG x0 ⟶ Z.t.G) := fun a =>
    haveI := Z.t.act.hom a
    postHom x0 (Z.t.act.act a)
  have hρ : ∀ a v, ρ a v = v ≫ Z.t.act.act a := fun _ _ => rfl
  have hcomb : ∀ {m : ℕ} (u : Fin m → (Sp (DualNumber Ω) ⟶ Z.t.G.left)) (hu : ∀ i, IsTanAtG Z.t x0 (u i))
      (a : Fin m → Ω) (W : tEpsG x0 ⟶ Z.t.G),
      IsCombAtG Z.t x0 u a W.left ↔ ∏ i, smHom x0 (a i) (ovT (hu i)) = W := fun u hu a W =>
    (isCombAtG_iff Z.t x0 (fun i => ovT (hu i)) a W.left).trans
      ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun V => V.left) h⟩
  have main := unique_coords (smHom x0) ρ ((RingOfIntegers.basis E).reindex (NumberField.equivReindex E).symm) χ hχ
    (smT_smT x0) (smT_unit x0) (smT_add x0) (fun r a v => (smT_post x0 a v _).symm)
    (fun v => by rw [hρ, Z.t.act.one, Category.comp_id])
    (fun r s v => by rw [hρ, hρ, hρ, Z.t.act.mul, Category.assoc])
    (fun r s v => by rw [hρ, hρ, hρ, Z.t.act.add, MonObj.comp_mul])
    (fun τ i => ovT (y.tan τ i)) (fun τ i => smT_zero_ovT _)
    (fun τ i r => by apply Over.OverMorphism.ext; exact y.eig τ i r)
    (fun τ v hv he => (existsUnique_congr fun a => hcomb (y.u τ) (y.tan τ) a v).1
      (y.basis τ v.left (isTanAtG_of v hv) fun r => congrArg (fun V => V.left) (he r)))
    e (ovT hw) (smT_zero_ovT hw)
  exact (existsUnique_congr fun a => hcomb _ (fun k => y.tan (e k).1 (e k).2) a (ovT hw)).2 main

end
