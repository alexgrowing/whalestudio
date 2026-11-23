import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchKapX
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SphericalFixesPureVacuumVectors
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolynomialMatchingInduction

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree
theorem polarization_match_square_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ g ∈ GfC X, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW 1, kapX X e hO.JX g) ΦD) (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1, kapX X e hO.JX g) Φ₀D) := by
  classical
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT R Rf hM Pi rf rl p p' _ g hg ΦD _ Φ₀D _ hPM
  rw [conjU_one_eq, conjU_one_eq]
  have hinf := GlobalTheory.T.archimedeanSupported_smul_transposeGram_finite_sub_one D X e hO.JX g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨T₀, hXT, hOn⟩ := hPM
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T₀ ∪ S₀)
  have ext : ∀ U : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf (T₀ ∪ U) ΦD Φ₀D := by
    intro U
    induction U using Finset.induction_on with
    | empty => rw [Finset.union_empty]; exact hOn
    | insert v U hv ih =>
      rw [Finset.union_insert]
      by_cases hvX : v ∈ Xc.T
      · rw [Finset.insert_eq_of_mem (Finset.mem_union_left _ (hXT hvX))]
        exact ih
      · exact GlobalTheory.ThK.PolynomialMatching.polMatchOn_insert _ _ _ Bs _ _ Γ Xc R Rf v (hM.fin.sph v hvX).1 _ _ _ ih
  have hOnS : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S ΦD Φ₀D := by
    have := ext S
    rwa [Finset.union_eq_right.2 (Finset.union_subset_left hTS)] at this
  have hU := hS₀ S (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have hOnK : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S (om (1, k) ΦD) (om' (1, k) Φ₀D) := by
    obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hOnS
    refine ⟨m, m', f, φ, f', φ', hφ, hφ', ?_, ?_, hsum⟩
    · rw [hΦ, map_sum]
      exact Finset.sum_congr rfl fun i _ => hU.1 (f i) (φ i) (hφ i).2.1 (hφ i).2.2
    · rw [hΦ', map_sum]
      exact Finset.sum_congr rfl fun j _ => hU.2 (f' j) (φ' j) (hφ' j).2.1 (hφ' j).2.2
  have split : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Φ, om (1, x * y) Φ = om (1, x) (om (1, y) Φ) := by
    intro x y Φ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Φ, om' (1, x * y) Φ = om' (1, x) (om' (1, y) Φ) := by
    intro x y Φ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S (om (1, (l'.map Prod.snd).prod * k) ΦD)
        (om' (1, (l'.map Prod.snd).prod * k) Φ₀D) := by
    intro l'
    induction l' with
    | nil => intro _; simpa using hOnK
    | cons x l' ih =>
      intro hx
      have h1 := hx x List.mem_cons_self
      have h2 := ih fun y hy => hx y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.prod_cons, mul_assoc]
      rw [split, split']
      exact _root_.GlobalTheory.T.polynomial_matching_induction hP _ _ _ Bs _ _ Γ Xc om om' R Rf hM S x.1 h1.1 x.2 h1.2 _ _ h2
  rw [hprod]
  exact ⟨S, hXT.trans (Finset.subset_union_left.trans hTS), key l hl⟩
end GlobalTheory.SquareAgree
end
end
