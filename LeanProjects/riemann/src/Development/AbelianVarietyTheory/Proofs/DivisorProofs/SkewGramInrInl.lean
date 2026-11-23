import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat.VacFix

theorem isHalf_of_mulG {D : D7} (S : HSp D) {n : ℕ} (ε : AE D) (x : Matrix (Fin n) (Fin S.rank) (AE D))
    (h : ∀ a b, ε * mulG S x a b = mulG S x a b) (a : Fin n) (b : Fin S.rank) : ε * x a b = x a b := by
  have h1 : ε • mulG S x = mulG S x := Matrix.ext h
  have h2 : divG S (ε • mulG S x) = ε • divG S (mulG S x) := Matrix.smul_mul _ _ _
  rw [h1, divG_mulG] at h2
  exact (congrFun (congrFun h2 a) b).symm

theorem hTens_eq_zero {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (hc : ∀ a, c (c a) = a)
    {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A)
    (h₁ : ∀ a b, JB (e (.inl a)) (e (.inr b)) = 0) (h₂ : ∀ a b, JB (e (.inr a)) (e (.inl b)) = 0)
    (ε : A) (hε : ε * c ε = 0) (x : Matrix (Fin n) (Fin d) A)
    (hl : ∀ a b, ε * x a (e (.inl b)) = x a (e (.inl b)))
    (hr : ∀ a b, ε * c (x a (e (.inr b))) = c (x a (e (.inr b)))) : hTens c JA JB x x = 0 := by
  unfold hTens
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  obtain ⟨b | b, rfl⟩ := e.surjective b <;> obtain ⟨l | l, rfl⟩ := e.surjective l
  · have u := congrArg c (hl k l)
    rw [map_mul] at u
    rw [← u, ← hl a b]
    linear_combination (x a (e (.inl b)) * JA a k * JB (e (.inl b)) (e (.inl l)) * c (x k (e (.inl l)))) * hε
  · rw [h₁, mul_zero, zero_mul]
  · rw [h₂, mul_zero, zero_mul]
  · have u := congrArg c (hr a b)
    rw [map_mul, hc] at u
    rw [← u, ← hr k l]
    linear_combination (x a (e (.inr b)) * JA a k * JB (e (.inr b)) (e (.inr l)) * c (x k (e (.inr l)))) * hε

theorem skewGram_inl_inr {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (a b) :
    skewGram A B e (e (.inl a)) (e (.inr b)) = 0 := by
  simp [skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem skewGram_inr_inl {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (a b) :
    skewGram A B e (e (.inr a)) (e (.inl b)) = 0 := by
  simp [skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem hTens_mixHalf {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) (ε : AE D)
    (hε : ε * cA D ε = 0) (γ : Pt G i j) (hγ : γ ∈ mixHalf e ε) :
    hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
  refine hTens_eq_zero (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) GlobalTheory.DualPairCheck.cA_cA e _ _
    (fun a b => ?_) (fun a b => ?_) ε hε γ (fun a b => ?_) (fun a b => ?_)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (skewGram_inl_inr _ _ e a b))).trans (map_zero _)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (skewGram_inr_inl _ _ e a b))).trans (map_zero _)
  · exact isHalf_of_mulG (negSp (spW G i j)) ε (colV e γ)ᵀ hγ.1 b a
  · refine isHalf_of_mulG (spV₁ G i j) ε ((γ.submatrix id fun k => e (.inr k)).map (cA D)) (fun a b => ?_) a b
    exact neg_injective ((mul_neg _ _).symm.trans (hγ.2 a b))

theorem psi_double {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ)
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (θ : 𝓞 E)
    (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (hγ : γ ∈ latAtV X Y v) :
    B.ψ (⅟(2 : AF F) * symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (2 • γ) (2 • γ)) = 1 := by
  have h2 : (2 : ℕ) • γ = (2 : AF F) • γ := by rw [two_smul, two_smul]
  rw [h2, GlobalTheory.LatVac.symp_smul_smul, ← mul_assoc, ← mul_assoc, invOf_mul_self, one_mul]
  refine GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 2 ?_ γ hγ γ hγ
  rw [map_ofNat]
  exact ofNat_mem _ 2

theorem vac_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ v : Pl D.host.F, (∀ u ∈ latPt e v, u ∈ latAtV Γ.V Γ.W v) →
      ∀ γ ∈ genPt e v, Acts (evFin D.host.F v) (Γ.M.co.rho W.ψ γ) (Γ.M.vac v) (Γ.M.vac v) := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT v hL γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM.vac v
  have h1 := hθ γ (hL γ (genPt_subset e v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, ε, hε, hγ⟩
    · exact psi_double _ Bs Γ.V Γ.W _ _ _ _ hT.base hT.geo.hV hT.geo.hW v θ γ' (hL γ' hγ')
    · unfold symp
      rw [hTens_mixHalf e Γ h.JWW ε hε.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul, h.ψ] at h1
  exact h1

end GlobalTheory.BigDat.VacFix

end
