import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSuccSpanMultiplicationStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH
open scoped Classical

namespace GlobalTheory.FockDegPf

open GlobalTheory.RealLift.PolRangePf GlobalTheory.KFixIrr

theorem totalDegree_pderiv_le_of {σ : Type} (i : σ) (g : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv i g).totalDegree ≤ g.totalDegree := by
  refine Finset.sup_le fun m hm => ?_
  have hc : MvPolynomial.coeff (m + Finsupp.single i 1) g ≠ 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    intro h
    rw [h, zero_mul] at hm
    exact hm rfl
  have h1 := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 hc)
  have h2 : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  rw [h2] at h1
  show (m.sum fun _ e => e) ≤ g.totalDegree
  omega

theorem heisOp_totalDegree_le {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (g : Formalism.BasicNotions.TH.Pol P Q R S) :
    (heisOp c g).totalDegree ≤ g.totalDegree + 1 := by
  let N := MvPolynomial.restrictTotalDegree (Ln P Q R S) ℂ (g.totalDegree + 1)
  have hr : ∀ l, raiB l g ∈ N := fun l => by
    rw [MvPolynomial.mem_restrictTotalDegree]
    unfold raiB
    split_ifs
    · rw [LinearMap.mulLeft_apply]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X]; omega
    · rw [LinearMap.neg_apply, MvPolynomial.totalDegree_neg]
      exact (totalDegree_pderiv_le_of _ g).trans (Nat.le_succ _)
  have hl : ∀ l, lowB l g ∈ N := fun l => by
    rw [MvPolynomial.mem_restrictTotalDegree]
    unfold lowB
    split_ifs
    · exact (totalDegree_pderiv_le_of _ g).trans (Nat.le_succ _)
    · rw [LinearMap.mulLeft_apply]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X]; omega
  have : heisOp c g ∈ N := by
    unfold heisOp
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    refine N.smul_mem _ (N.sum_mem fun l _ => ?_)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    exact N.sub_mem (N.smul_mem _ (hr l)) (N.smul_mem _ (hl l))
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).1 this

theorem degLE_zero_eq {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} :
    GlobalTheory.KFixIrr.degLE ι P Q R S 0 = Submodule.span ℂ {PiTensorProduct.tprod ℂ (fun _ : ι => (1 : Formalism.BasicNotions.TH.Pol P Q R S))} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    have h0 : ∀ w, (f w).totalDegree = 0 := fun w => by
      have := Finset.single_le_sum (f := fun w => (f w).totalDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
      omega
    have hf' : f = fun w => MvPolynomial.coeff 0 (f w) • (1 : Formalism.BasicNotions.TH.Pol P Q R S) := by
      funext w
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
      exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (h0 w)
    rw [hf', MultilinearMap.map_smul_univ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact tprod_mem_degLE _ (by simp)

theorem atPl_heisOp_mem {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (w : ι) (c : Matrix (Ix P Q) (Ix R S) ℂ) (k : ℕ)
    (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) (hT : T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S k) :
    atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (heisOp c) T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S (k + 1) := by
  have hle : GlobalTheory.KFixIrr.degLE ι P Q R S k ≤ (GlobalTheory.KFixIrr.degLE ι P Q R S (k + 1)).comap
      (atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (heisOp c)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, GlobalTheory.RealLift.atPl_tprod]
    refine tprod_mem_degLE _ ?_
    have e1 : ∑ v, (Function.update f w (heisOp c (f w)) v).totalDegree =
        ∑ v, Function.update (fun v => (f v).totalDegree) w (heisOp c (f w)).totalDegree v := by
      refine Finset.sum_congr rfl fun v _ => ?_
      exact Function.apply_update (fun _ p => MvPolynomial.totalDegree p) f w _ v
    rw [e1, Finset.sum_update_of_mem (Finset.mem_univ w)]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ w)] at hf
    have := heisOp_totalDegree_le c (f w)
    omega
  exact hle hT

theorem degLE_succ_le {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (k : ℕ) :
    GlobalTheory.KFixIrr.degLE ι P Q R S (k + 1) ≤ GlobalTheory.KFixIrr.degLE ι P Q R S k ⊔ Submodule.span ℂ
      {T' | ∃ (w : ι) (l : Ln P Q R S), ∃ T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S k,
        T' = atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w
          (LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S)) T} := by
  exact GlobalTheory.T.degree_succ_span_multiplication k

theorem fockDeg_eq_map : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d P Q R S : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : InfinitePlace F → Matrix (Fin n) (Formalism.BasicNotions.TH.Ix P Q) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ)
    (Φ : GlobalTheory.RealLift.Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → IsStd ψ →
    GlobalTheory.RealLift.Framed τ (incM F X.J) (incM F W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Formalism.BasicNotions.TH.Jm P Q) →
    (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S) → GlobalTheory.RealLift.IsFockMap ψ τ M.co A C Φ →
    ∀ k, fockDeg M ψ τ k = (GlobalTheory.KFixIrr.degLE (InfinitePlace F) P Q R S k).map Φ := by
  intro hL _hD hV F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  have uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂ := fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have der : ∀ u, At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix P Q) (Ix R S) ℂ) (e : ℂ),
      A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm R S * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • ((A w * Jm P Q) * c * (Jm R S * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm P Q * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm R S)) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPl_twist_one, map_smul]
  intro k
  induction k with
  | zero =>
    rw [fockDeg_zero, degLE_zero_eq, Submodule.map_span, Set.image_singleton]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro f₀ hf₀
      obtain ⟨ε, hε⟩ := hf₀
      obtain ⟨z, hz⟩ := hV F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      rw [hz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span gauss1
  | succ k ih =>
    rw [fockDeg_succ, ih]
    apply le_antisymm
    · refine sup_le (Submodule.map_mono (degLE_mono (Nat.le_succ k))) (Submodule.span_le.2 ?_)
      rintro f₁ ⟨u, hu, f, ⟨T, hT, rfl⟩, hd⟩
      rw [uniq u _ _ _ hd (der u hu _ (decomp u) T)]
      refine ⟨_, ?_, rfl⟩
      rw [sumPl, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun w _ => atPl_heisOp_mem w _ k T hT
    · rw [Submodule.map_le_iff_le_comap]
      refine (degLE_succ_le k).trans (sup_le ?_ (Submodule.span_le.2 ?_))
      · intro T hT
        exact Submodule.mem_sup_left ⟨T, hT, rfl⟩
      · rintro _ ⟨w, l, T, hT, rfl⟩
        let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
          (GlobalTheory.KFixIrr.degLE (InfinitePlace F) P Q R S k).map Φ ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧
                         ∃ f ∈ (GlobalTheory.KFixIrr.degLE (InfinitePlace F) P Q R S k).map Φ, ActsD (evI F) (M.heisLine ψ u) f f₁}
        let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) :=
          { carrier := {L | atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w L T ∈ N.comap Φ}
            add_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq] at ha hb ⊢
              rw [atPl_add', LinearMap.add_apply]; exact Submodule.add_mem _ ha hb
            zero_mem' := by
              simp only [Set.mem_setOf_eq]; rw [atPl_zero']; exact Submodule.zero_mem _
            smul_mem' := fun c a ha => by
              simp only [Set.mem_setOf_eq] at ha ⊢
              rw [atPl_smul', LinearMap.smul_apply]; exact Submodule.smul_mem _ c ha }
        have hK : Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) ≤ K := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨c, rfl⟩
          obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
            (fun w' => A w' * Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w' * (C w')ᵀ)
          have hs : sumPl (fun w' => heisOp (Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w')) T =
              atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (heisOp c) T := by
            rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]
            · simp
            · intro b _ hb; simp [Function.update_of_ne hb, heisOp_zero, atPl_zero']
            · simp
          have hmem : Φ (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (heisOp c) T) ∈ N := by
            rw [← hs]
            exact Submodule.mem_sup_right (Submodule.subset_span ⟨u, hu, Φ T, ⟨T, hT, rfl⟩, der u hu _ hu' T⟩)
          exact hmem
        exact hK (mulX_mem_span l)

end GlobalTheory.FockDegPf
