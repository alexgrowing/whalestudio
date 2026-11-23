import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertForm.FormEx

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem arFun_eq_rename (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) {ι κ : Type} [Fintype ι] [Fintype κ]
    {L : ι → HermLB p} {M : κ → HermLB p} {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} {Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun L D Φ) (hΨ : IsArFun M D Ψ) (r : ι → κ) (hr : ∀ i, M (r i) = L i) :
    Φ = Ψ ∘ₗ (MvPolynomial.rename r : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial κ ℝ).toLinearMap := by
  have h := ((H.arIso k X p D hX).2 κ M Ψ hΨ).2.2 ι L (fun i => Pi.single (r i) 1) (fun i => by
    rw [← hr i]; exact isometric_comb_single M (r i))
  rw [Model.isArFun_unique hX hΦ h]
  congr 2
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [MvPolynomial.aeval_X, lin_single, MvPolynomial.rename_X]

def famFn (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) {n : ℕ} (f : Fin n → HermLB p) : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ :=
  Classical.choose (((H.arExists k X p D hX).2 (Fin n) f).1)

theorem famFn_spec (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) {n : ℕ} (f : Fin n → HermLB p) :
    IsArFun f D (famFn H hX f) :=
  Classical.choose_spec (((H.arExists k X p D hX).2 (Fin n) f).1)

def enum (S : Finset (HermLB p)) (i : Fin S.card) : HermLB p := (S.equivFin.symm i).1

theorem enum_injective (S : Finset (HermLB p)) : Function.Injective (enum S) :=
  fun _ _ h => S.equivFin.symm.injective (Subtype.ext h)

theorem enum_equivFin (S : Finset (HermLB p)) {x : HermLB p} (hx : x ∈ S) : enum S (S.equivFin ⟨x, hx⟩) = x := by
  simp [enum]

theorem range_enum (S : Finset (HermLB p)) : Set.range (enum S) = S :=
  Set.ext fun x => ⟨by rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2, fun hx => ⟨_, enum_equivFin S hx⟩⟩

def total (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) : MvPolynomial (HermLB p) ℝ →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials (HermLB p) ℝ).constr ℝ fun m =>
    famFn H hX (enum m.support) (MvPolynomial.monomial (m.comapDomain (enum m.support) (enum_injective _).injOn) 1)

theorem total_rename (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) {ι : Type} [Fintype ι] (L : ι → HermLB p)
    {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun L D Φ) :
    total H hX ∘ₗ (MvPolynomial.rename L : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial (HermLB p) ℝ).toLinearMap = Φ := by
  refine (MvPolynomial.basisMonomials ι ℝ).ext fun m => ?_
  rw [MvPolynomial.coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.rename_monomial,
    total, ← congrFun (MvPolynomial.coe_basisMonomials (HermLB p) ℝ) (Finsupp.mapDomain L m), Module.Basis.constr_basis]
  set n := Finsupp.mapDomain L m
  let T : Finset (HermLB p) := Finset.univ.image L
  have hL (i : ι) : L i ∈ T := Finset.mem_image_of_mem L (Finset.mem_univ i)
  have hST : n.support ⊆ T := fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact hL i
  have hS (i : Fin n.support.card) : enum n.support i ∈ T := hST (by rw [← Finset.mem_coe, ← range_enum]; exact ⟨i, rfl⟩)
  have k1 := arFun_eq_rename H hX hΦ (famFn_spec H hX (enum T)) (fun i => T.equivFin ⟨L i, hL i⟩)
    fun i => enum_equivFin T (hL i)
  have k2 := arFun_eq_rename H hX (famFn_spec H hX (enum n.support)) (famFn_spec H hX (enum T))
    (fun i => T.equivFin ⟨_, hS i⟩) fun i => enum_equivFin T (hS i)
  rw [k1, k2, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.rename_monomial, MvPolynomial.rename_monomial]
  congr 3
  refine Finsupp.mapDomain_injective (M := ℕ) (enum_injective T) ?_
  rw [← Finsupp.mapDomain_comp (M := ℕ), ← Finsupp.mapDomain_comp (M := ℕ)]
  have e1 : enum T ∘ (fun i => T.equivFin ⟨_, hS i⟩) = enum n.support := funext fun i => enum_equivFin T (hS i)
  have e2 : enum T ∘ (fun i => T.equivFin ⟨L i, hL i⟩) = L := funext fun i => enum_equivFin T (hL i)
  rw [e1, e2, Finsupp.mapDomain_comapDomain _ (enum_injective _) _ (by rw [range_enum])]

def linOf : Cl p →ₗ[ℝ] MvPolynomial (HermLB p) ℝ := Finsupp.linearCombination ℝ fun L => MvPolynomial.X L

def num (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) : Form (Cl p) D :=
  (total H hX).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra ℝ (Fin (D + 1)) (MvPolynomial (HermLB p) ℝ)).compLinearMap fun _ => linOf)

theorem num_apply (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) (v : Fin (D + 1) → Cl p) :
    num H hX v = total H hX (∏ j, linOf (v j)) := by
  simp [num]

end GlobalTheory.VertForm.FormEx

namespace GlobalTheory.VertForm

theorem exists_symm_arForm : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ num : Form (Cl p) D, IsArForm D num ∧ IsSymm num := by
  intro H k _ X _ p D hX
  refine ⟨FormEx.num H hX, fun ι _ L Φ hΦ a => ?_, fun v π => ?_⟩
  · rw [FormEx.num_apply, ← FormEx.total_rename H hX L hΦ, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [lin, FormEx.linOf, map_sum, cl, Finsupp.linearCombination_single, MvPolynomial.smul_eq_C_mul]
  · rw [FormEx.num_apply, FormEx.num_apply]
    congr 1
    exact Equiv.prod_comp π fun j => FormEx.linOf (v j)

end GlobalTheory.VertForm
