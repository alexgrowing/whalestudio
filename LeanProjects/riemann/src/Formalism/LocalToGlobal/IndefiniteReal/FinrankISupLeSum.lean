import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Dims

theorem li_cpt (σ : K →+* ℂ) {n d : ℕ} (v : Fin d → Fin n → K) (hv : LinearIndependent K v) :
    LinearIndependent ℂ (fun i => cpt σ (v i)) := by
  classical
  let M : Matrix (Fin n) (Fin d) K := Matrix.of fun r i => v i r
  have hMv : ∀ c : Fin d → K, M.mulVec c = ∑ i, c i • v i := by
    intro c; funext r
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinj : LinearMap.ker M.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∑ i, c i • v i = 0 := by rw [← hMv]; exact hc
    funext i
    exact Fintype.linearIndependent_iff.1 hv c h0 i
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin hinj
  let N : Matrix (Fin d) (Fin n) K := LinearMap.toMatrix' g
  have hNM : N * M = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
    exact this
  have hNMc : N.map σ * M.map σ = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hMc : ∀ c : Fin d → ℂ, (M.map σ).mulVec c = ∑ i, c i • cpt σ (v i) := by
    intro c; funext r
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, cpt, mul_comm]
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : (M.map σ).mulVec c = 0 := by rw [hMc]; exact hc
  have h2 : c = (N.map σ * M.map σ).mulVec c := by rw [hNMc, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero] at h2
  rw [h2]; rfl

theorem finrank_le_cpt {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℂ] E) (hL : Function.Injective L) (T : Submodule ℂ E) (S : Submodule K (Fin n → K))
    (hS : ∀ x ∈ S, L (cpt σ x) ∈ T) : finrank K S ≤ finrank ℂ (T ⊓ LinearMap.range L : Submodule ℂ E) := by
  classical
  let bs := Module.finBasis K S
  let v : Fin (finrank K S) → Fin n → K := fun i => (bs i : Fin n → K)
  have hv : LinearIndependent K v := bs.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hc := li_cpt σ v hv
  have hw : LinearIndependent ℂ (fun i => L (cpt σ (v i))) := hc.map' L (LinearMap.ker_eq_bot.2 hL)
  let w' : Fin (finrank K S) → (T ⊓ LinearMap.range L : Submodule ℂ E) :=
    fun i => ⟨L (cpt σ (v i)), hS _ (bs i).2, ⟨_, rfl⟩⟩
  have hw' : LinearIndependent ℂ w' := LinearIndependent.of_comp (T ⊓ LinearMap.range L).subtype hw
  simpa using hw'.fintype_card_le_finrank

variable {R V : Type} [Field R] [AddCommGroup V] [Module R V] [FiniteDimensional R V]

theorem finrank_iSup_le_sum {ι : Type} [Fintype ι] (S : ι → Submodule R V) :
    finrank R (⨆ i, S i : Submodule R V) ≤ ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) ≤ ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha]
      exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

theorem finrank_iSup_eq_sum {ι : Type} [Fintype ι] (S : ι → Submodule R V) (hS : iSupIndep S) :
    finrank R (⨆ i, S i : Submodule R V) = ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) = ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
      have hd : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (y := (s : Set ι)) (by exact_mod_cast ha)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
      rw [hd.eq_bot, finrank_bot, add_zero] at h
      exact h
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

theorem eq_of_le_of_sum_le {ι : Type} [Fintype ι] (a c : ι → ℕ) (h : ∀ i, a i ≤ c i) (hs : ∑ i, c i ≤ ∑ i, a i) (i : ι) :
    a i = c i := by
  classical
  have hs' : ∑ i, a i = ∑ i, c i := le_antisymm (Finset.sum_le_sum fun i _ => h i) hs
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs' i (Finset.mem_univ i)

end Dims

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem indep_of_orth {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T : Bs.Ix → Submodule ℂ E)
    (h : ∀ p q, p ≠ q → ∀ e ∈ T p, ∀ e' ∈ T q, ⟪e, e'⟫_ℂ = 0) : iSupIndep T := by
  apply OrthogonalFamily.independent
  rw [orthogonalFamily_iff_pairwise]
  intro p q hpq
  exact (Submodule.isOrtho_iff_inner_eq).2 (h p q hpq)

theorem finrank_Ep (hW : (lv (fc X.zs) b).WF) (h2 : X.H2 cr b) (h3 : X.H3 cr b) (hE : X.PartsE b) (p : Bs.Ix) :
    finrank K (X.Ep cr b p) = finrank ℂ (X.EEp p ⊓ X.EEl b : Submodule ℂ X.EE) := by
  have hEQ : ∀ q, X.Ep cr b q = (lv (fc X.zs) b).Qp Bs.μ0 q := by
    intro q; ext x; exact (h3 q x).symm
  have hle : ∀ q, finrank K (X.Ep cr b q) ≤ finrank ℂ (X.EEp q ⊓ X.EEl b : Submodule ℂ X.EE) := by
    intro q
    have := finrank_le_cpt Bs.v0.embedding (X.iC cr b Bs.μ0) h2.1 (X.EEp q) (X.Ep cr b q) (fun x hx => hx)
    rwa [h2.2.2] at this
  refine eq_of_le_of_sum_le _ _ hle ?_ p
  have hK : (lv (fc X.zs) b).dQ Bs.μ0 ≤ ∑ q, finrank K (X.Ep cr b q) := by
    have h := finrank_iSup_le_sum ((lv (fc X.zs) b).Qp Bs.μ0)
    rw [hW.Qp_top, finrank_top, Module.finrank_fin_fun] at h
    exact h.trans (Finset.sum_congr rfl fun q _ => by rw [hEQ q]).le
  have hC : ∑ q, finrank ℂ (X.EEp q ⊓ X.EEl b : Submodule ℂ X.EE) ≤ (lv (fc X.zs) b).dQ Bs.μ0 := by
    rw [← finrank_iSup_eq_sum _ (indep_of_orth _ hE.1)]
    calc finrank ℂ (⨆ q, X.EEp q ⊓ X.EEl b : Submodule ℂ X.EE) ≤ finrank ℂ (X.EEl b) :=
          Submodule.finrank_mono (iSup_le fun q => inf_le_right)
      _ = finrank ℂ (LinearMap.range (X.iC cr b Bs.μ0)) := by rw [h2.2.2]
      _ ≤ _ := (LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun ℂ).le
  exact hC.trans hK

theorem finrank_WpK (hp : X.H4pos) (hk : X.KForm b) (he : X.EWnorm b)
    (hT : (lv (fc X.zs) b).Types) (h5 : X.H5 cr b) (hr : X.RATth cr b) (h3w : X.H3W cr b) (hPW : X.PartsW b)
    (j : Bs.J) (p : Bs.Ix) :
    finrank K (X.WpK b j p) = finrank ℂ (X.Wp j p ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j)) := by
  have hw := X.principal_form_injective b hk he (hp.2.2 b) j
  have hu : ∀ q, finrank K (X.WpK b j q) ≤
      finrank ℂ (X.Wp j q ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j)) :=
    fun q => finrank_le_cpt Bs.v0.embedding (X.w0C b j) hw (X.Wp j q) (X.WpK b j q) (fun x hx => hx)
  have hinj : Function.Injective (X.liftMat cr b j Bs.μ0).mulVecLin := by
    intro x y hxy
    apply cpt_injective Bs.v0.embedding
    apply (h5 j Bs.μ0).1
    rw [← X.key_lift cr b h5 hr, ← X.key_lift cr b h5 hr]
    exact congrArg (fun z => X.w0C b j (cpt Bs.v0.embedding z)) hxy
  have hl : ∀ q, finrank K ((lv (fc X.zs) b).Zp j Bs.μ0 q) ≤ finrank K (X.WpK b j q) := by
    intro q
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj ((lv (fc X.zs) b).Zp j Bs.μ0 q))]
    apply Submodule.finrank_mono
    rintro _ ⟨x, hx, rfl⟩
    show X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j Bs.μ0).mulVec x)) ∈ X.Wp j q
    rw [X.key_lift cr b h5 hr]
    exact (h3w j q x).1 hx
  have hsum : ∀ q, finrank K ((lv (fc X.zs) b).Zp j Bs.μ0 q) =
      finrank ℂ (X.Wp j q ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j)) := by
    refine eq_of_le_of_sum_le _ _ (fun q => (hl q).trans (hu q)) ?_
    have hK : (lv (fc X.zs) b).dZ j Bs.μ0 ≤ ∑ q, finrank K ((lv (fc X.zs) b).Zp j Bs.μ0 q) := by
      have h := finrank_iSup_le_sum ((lv (fc X.zs) b).Zp j Bs.μ0)
      rwa [hT j, finrank_top, Module.finrank_fin_fun] at h
    refine le_trans ?_ hK
    rw [← finrank_iSup_eq_sum _ (indep_of_orth _ (hPW j).1)]
    calc finrank ℂ (⨆ q, X.Wp j q ⊓ LinearMap.range (X.w0C b j) : Submodule ℂ (X.W j))
          ≤ finrank ℂ (LinearMap.range (X.w0C b j)) := Submodule.finrank_mono (iSup_le fun q => inf_le_right)
      _ = finrank ℂ (LinearMap.range (X.tC cr b j Bs.μ0)) := by rw [(h5 j Bs.μ0).2]
      _ = _ := by rw [LinearMap.finrank_range_of_inj (h5 j Bs.μ0).1, Module.finrank_fin_fun]
  exact le_antisymm (hu p) ((hsum p).symm.le.trans (hl p))

theorem cutDims : X.CutDims cr b := by
  intro hW hp hk he hT h2 _ h3 h5 hr h3w hE hPW hD j p
  show finrank K (X.WpK b j p) = finrank K (X.Ep cr b p)
  rw [X.finrank_WpK cr b hp hk he hT h5 hr h3w hPW j p, hD j p, X.finrank_Ep cr b hW h2 h3 hE p]

end CxData

end Formalism.IndefR.Cx
