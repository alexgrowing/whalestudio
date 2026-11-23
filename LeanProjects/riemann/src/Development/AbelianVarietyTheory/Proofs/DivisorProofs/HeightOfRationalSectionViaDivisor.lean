import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermSumZeroOfPolynomialIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjectiveStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier

namespace GlobalTheory.VertMix

theorem sum_perm_eq_zero {D : ℕ} (E : (Fin D → Fin D) → ℝ)
    (h : ∀ n : Fin D → ℤ, ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * E a = 0) :
    ∑ σ : Equiv.Perm (Fin D), E σ = 0 :=
  GlobalTheory.T.perm_sum_zero_of_polynomial_identity D E h

theorem isProjOver_of_vertical {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Z, ⊤)] :
    IsProjOver (strHom (ZMod l) Z) :=
  GlobalTheory.T.closed_subscheme_mod_l_projective k X p D hX Z i l

theorem topSelf_comb_pull {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {κ : Type} [Field κ]
    {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = D) (i : Z ⟶ X)
    (N : Fin D → HermLB p) (n : Fin D → ℤ) :
    (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ) =
      ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * (interNum κ (structureModule Z) (fun j => (N (a j)).B.pull i) : ℝ) := by
  have HD := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := D)
    (by rw [QCoh.suppDim_structureModule, hd])
  have hL : ∀ j, ((N j).B.pull i).IsLB := fun j => LB.isLB_pull (N j).isLB i
  have e := HD.interNum_of_cls_eq_sum (L := fun j => (N j).B.pull i) hL (Q := fun _ => (comb N n).B.pull i)
    (fun _ => LB.isLB_pull (comb N n).isLB i) (fun _ => n) fun _ => by
      rw [CechPic.cls_pull (comb N n).isLB, GenFibreSecs.cls_comb, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, CechPic.cls_pull (N j).isLB]
  rw [topSelf_def, e]
  push_cast
  rfl

end GlobalTheory.VertMix

namespace GlobalTheory.VertMix

theorem diag_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ}
    (H : Published.ArMix) (hX : IsArithVar p D) {ι : Type} [Fintype ι] {M : HermLB p} {N : ι → HermLB p}
    {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun (fun o : Option ι => o.elim M N) D Φ) (n : ι → ℤ)
    {h : X → ℝ} (hh : (comb N n).IsArithHeight h) {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r)
    (h1 : ∀ σ, ∀ y ∈ offSupp p σ (M.div hr), logNorm (M.φ σ) r y = 0) :
    Φ (MvPolynomial.X none * MvPolynomial.rename some (lin fun i => (n i : ℝ)) ^ D) = ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z := by
  have e : (comb N n).archInt M D hr = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
    rw [Weight.chernInt_congr (g := fun _ => 0) (isOpen_offSupp _).measurableSet (h1 σ)]
    simp [Weight.chernInt]
  rw [(H k X p D hX ι M N Φ hΦ n h hh r hr).2, e, sub_zero]

theorem local_expansion {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (N : Fin D → HermLB p) (z : X) (l : ℕ) (dz : ℝ)
    (hz : ∃ (_ : Fact l.Prime) (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z)
      (_ : Algebra (ZMod l) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = D ∧
        dz = interNum (ZMod l) (structureModule Z) (fun j => (N j).B.pull i)) :
    ∃ T : (Fin D → Fin D) → ℝ, (∀ σ : Equiv.Perm (Fin D), T σ = dz) ∧
      ∀ (n : Fin D → ℤ) (h : X → ℝ), (comb N n).IsArithHeight h →
        h z = (∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * T a) * Real.log l := by
  obtain ⟨_, Z, i, _, _, _, rfl, hdim, hdz⟩ := hz
  have hp := isProjOver_of_vertical hX i l
  refine ⟨fun a => (interNum (ZMod l) (structureModule Z) (fun j => (N (a j)).B.pull i) : ℝ), fun σ => ?_,
    fun n h hh => ?_⟩
  · rw [hdz]
    exact congrArg _ (interNum_comp_perm (ZMod l) (structureModule Z) (L := fun j => (N j).B.pull i)
      (fun j => LB.isLB_pull (N j).isLB i) σ)
  · rw [hh.vertical Z i (ZMod l) D hdim, Nat.card_zmod, topSelf_comb_pull hp hdim i N n]

end GlobalTheory.VertMix

namespace GlobalTheory.VertMix

theorem expand {D : ℕ} (Φ : MvPolynomial (Option (Fin D)) ℝ →ₗ[ℝ] ℝ) (n : Fin D → ℤ) :
    Φ (MvPolynomial.X none * MvPolynomial.rename some (lin fun i => (n i : ℝ)) ^ D) =
      ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) *
        Φ (MvPolynomial.X none * ∏ j, MvPolynomial.X (some (a j))) := by
  have e : MvPolynomial.rename some (lin fun i => (n i : ℝ)) ^ D =
      ∑ a : Fin D → Fin D, MvPolynomial.C (∏ j, (n (a j) : ℝ)) * ∏ j, MvPolynomial.X (some (a j)) := by
    rw [← Fin.prod_const, lin, map_sum, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X, Finset.prod_mul_distrib, map_prod]
  rw [e, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

theorem vertMix : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ num : Form (Cl p) D, IsArForm D num → ∀ (M : HermLB p)
    (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (∀ σ, ∀ y ∈ offSupp p σ (M.div hr), logNorm (M.φ σ) r y = 0) →
    ∀ (N : Fin D → HermLB p) (ℓ : X → ℕ) (d : X → ℝ), (∀ z, (M.div hr).mult z ≠ 0 → ∃ (_ : Fact (ℓ z).Prime)
      (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (_ : Algebra (ZMod (ℓ z)) Γ(Z, ⊤)),
      i (genericPoint Z) = z ∧ topologicalKrullDim Z = D ∧
        d z = interNum (ZMod (ℓ z)) (structureModule Z) (fun j => (N j).B.pull i)) →
    num (Fin.cons (cl M) fun j => cl (N j)) = ∑ᶠ z, ((M.div hr).mult z : ℝ) * d z * Real.log (ℓ z) := by
  intro hP k _ X _ _ p D hX num hnum M r hr h1 N ℓ d hd
  have HC := hP.p4
  obtain ⟨Φ, hΦ⟩ := ((HC.arExists k X p D hX).2 (Option (Fin D)) (fun o => o.elim M N)).1

  have e1 : num (Fin.cons (cl M) fun j => cl (N j)) =
      Φ (MvPolynomial.X none * ∏ j : Fin D, MvPolynomial.X (some j)) := by
    let c : Fin (D + 1) → Option (Fin D) := Fin.cons none some
    have := hnum (Option (Fin D)) (fun o => o.elim M N) Φ hΦ (fun j => Pi.single (c j) 1)
    have hl (o : Option (Fin D)) : lin (Pi.single o (1 : ℝ)) = MvPolynomial.X o := by
      rw [lin, Finset.sum_eq_single o (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simp
    have hs (o : Option (Fin D)) : ∑ i, (Pi.single o (1 : ℝ) : Option (Fin D) → ℝ) i • cl ((fun o => o.elim M N) i) =
        cl ((fun o => o.elim M N) o) := by
      rw [Finset.sum_eq_single o (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simp
    simp only [hl, hs] at this
    rw [Fin.prod_univ_succ] at this
    refine (Eq.trans ?_ this.symm)
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl

  have := hX.isNoetherian
  have hfin := CartierDiv.finite_support_mult (Z := X) (M.div hr)
  set S := hfin.toFinset
  have hS (z : X) : z ∈ S ↔ (M.div hr).mult z ≠ 0 := by simp [S]
  have hT (z : X) : ∃ T : (Fin D → Fin D) → ℝ, (M.div hr).mult z ≠ 0 → (∀ σ : Equiv.Perm (Fin D), T σ = d z) ∧
      ∀ (n : Fin D → ℤ) (h : X → ℝ), (comb N n).IsArithHeight h →
        h z = (∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * T a) * Real.log (ℓ z) := by
    by_cases hz : (M.div hr).mult z = 0
    · exact ⟨0, fun h => absurd hz h⟩
    · obtain ⟨T, hT⟩ := local_expansion hX N z (ℓ z) (d z) (hd z hz)
      exact ⟨T, fun _ => hT⟩
  choose T hT using hT

  let E : (Fin D → Fin D) → ℝ := fun a => Φ (MvPolynomial.X none * ∏ j, MvPolynomial.X (some (a j))) -
    ∑ z ∈ S, ((M.div hr).mult z : ℝ) * Real.log (ℓ z) * T z a
  have hE : ∀ n : Fin D → ℤ, ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * E a = 0 := by
    intro n
    obtain ⟨h, hh⟩ := (HC.arExists k X p D hX).1 (comb N n)
    have e2 := diag_eq HC.arMix hX hΦ n hh hr h1
    rw [expand] at e2
    rw [finsum_eq_sum_of_support_subset _ (s := S) fun z hz => (hS z).2 fun h0 => hz (by simp [h0])] at e2
    have e3 : ∑ z ∈ S, ((M.div hr).mult z : ℝ) * h z = ∑ z ∈ S, ((M.div hr).mult z : ℝ) *
        ((∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * T z a) * Real.log (ℓ z)) :=
      Finset.sum_congr rfl fun z hz => by rw [((hT z ((hS z).1 hz)).2 n h hh)]
    rw [e3] at e2
    have e4 : ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * E a =
        ∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * Φ (MvPolynomial.X none * ∏ j, MvPolynomial.X (some (a j))) -
          ∑ z ∈ S, ((M.div hr).mult z : ℝ) * ((∑ a : Fin D → Fin D, (∏ j, (n (a j) : ℝ)) * T z a) * Real.log (ℓ z)) := by
      simp only [E, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      exact Finset.sum_comm.trans (Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun a _ => by ring)
    rw [e4, ← e2, sub_self]
  have hsum := sum_perm_eq_zero E hE
  have hconst (σ : Equiv.Perm (Fin D)) : E σ = E (Equiv.refl (Fin D)) := by
    simp only [E]
    congr 1
    · congr 2
      exact Equiv.prod_comp σ fun j => MvPolynomial.X (some j)
    · refine Finset.sum_congr rfl fun z hz => ?_
      rw [(hT z ((hS z).1 hz)).1 σ, (hT z ((hS z).1 hz)).1 (Equiv.refl _)]
  rw [Finset.sum_congr rfl fun σ _ => hconst σ, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, mul_eq_zero] at hsum
  have hE0 : E (Equiv.refl (Fin D)) = 0 := hsum.resolve_left (by exact_mod_cast (Nat.factorial_pos D).ne')
  simp only [E, sub_eq_zero] at hE0
  rw [e1, finsum_eq_sum_of_support_subset _ (s := S) fun z hz => (hS z).2 fun h0 => hz (by simp [h0])]
  refine hE0.trans (Finset.sum_congr rfl fun z hz => ?_)
  rw [(hT z ((hS z).1 hz)).1 (Equiv.refl _)]
  ring

end GlobalTheory.VertMix
