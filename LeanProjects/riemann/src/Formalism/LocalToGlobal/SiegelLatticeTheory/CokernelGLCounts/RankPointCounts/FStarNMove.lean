import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFwd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus

noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace NMoveP

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem hsw (x y : S.V) : S.hT y x = star (S.hT x y) := PI.ScalarPairDr.W.hT_swap S x y

theorem hT_smulL (a : E) (x v : S.V) : S.hT (a • x) v = star a * S.hT x v := by
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem spanL {ι : Type*} (x : ι → S.V) (y : S.V) (h : ∀ i, S.hT (x i) y = 0) :
    ∀ u ∈ Submodule.span E (Set.range x), S.hT u y = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact h i
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [hT_smulL, ha, mul_zero]

theorem spanR {ι : Type*} (x : ι → S.V) (y : S.V) (h : ∀ i, S.hT y (x i) = 0) :
    ∀ u ∈ Submodule.span E (Set.range x), S.hT y u = 0 := by
  intro u hu
  have : Submodule.span E (Set.range x) ≤ LinearMap.ker (S.hT y) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  exact this hu

variable {S} {r : ℕ}

theorem fvecC {T : E} (F : FlagG S r T) (i : Fin r) : F.fvec i.castSucc = F.e i :=
  PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc F i

theorem fvecL {T : E} (F : FlagG S r T) : F.fvec (Fin.last r) = F.z :=
  PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last F

theorem hT_f_e {T : E} (F : FlagG S r T) (a : Fin (r + 1)) (c : Fin r) : S.hT (F.fvec a) (F.e c) = 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · rw [fvecL]; exact PI.UnitaryGroupMassFormula.BetaLUniq.GN.hT_z_e F c
  · rw [fvecC]; exact F.e_iso i c

theorem hT_f_X {T : E} (F : FlagG S r T) (a : Fin (r + 1)) {x : S.V} (hx : x ∈ F.X) : S.hT (F.fvec a) x = 0 :=
  spanR S F.e _ (fun c => hT_f_e F a c) x hx

theorem hT_X_X {T : E} (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 :=
  spanL S F.e y (fun c => by rw [← fvecC F c]; exact hT_f_X F _ hy) x hx

theorem gram_flag {T : E} (P Q : FlagG S r T) (a c : Fin (r + 1)) :
    S.hT (Q.fvec a) (Q.fvec c) = S.hT (P.fvec a) (P.fvec c) := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · refine Fin.lastCases ?_ (fun j => ?_) c
    · rw [fvecL, fvecL, Q.z_norm, P.z_norm]
    · rw [fvecL, fvecL, fvecC, fvecC, PI.UnitaryGroupMassFormula.BetaLUniq.GN.hT_z_e, PI.UnitaryGroupMassFormula.BetaLUniq.GN.hT_z_e]
  · refine Fin.lastCases ?_ (fun j => ?_) c
    · rw [fvecL, fvecL, fvecC, fvecC, Q.z_orth, P.z_orth]
    · rw [fvecC, fvecC, fvecC, fvecC, Q.e_iso, P.e_iso]

theorem hermitian_double_sum_expand {ι : Type*} [Fintype ι] (x : ι → S.V) (g g' : ι → E) :
    S.hT (∑ i, g i • x i) (∑ j, g' j • x j) = ∑ i, ∑ j, star (g i) * (g' j * S.hT (x i) (x j)) := by
  simp only [map_sum, LinearMap.sum_apply, hT_smulL, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable (S)

theorem exists_move {T T' : E} (F : FlagG S r T) (P Q : FlagG S r T')
    (hZ : Zhat F P = Zhat F Q) (hG : Gflag F Q ≠ 0)
    (hom : ∀ c : Fin (r + 1) → E, (∀ a, S.hT (F.e a) (∑ b, c b • P.fvec b) = 0) →
      ∑ b, c b • (Q.fvec b - P.fvec b) ∈ F.X) :
    ∃ n : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (n x) (n y) = S.hT x y) ∧ (∀ i, n (F.fvec i) = F.fvec i) ∧
      (∀ b, n (P.fvec b) = Q.fvec b) ∧ (∀ x ∈ orth S F.X, n x - x ∈ F.X) := by
  have hGP : Gflag F P ≠ 0 := by
    have : Gflag F P = Gflag F Q := by unfold Gflag Dl; rw [hZ]
    rwa [this]

  let b₂ : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim F.fvec P.fvec
  let tg : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim F.fvec Q.fvec
  let U : Submodule E S.V := Submodule.span E (Set.range b₂)
  let W : Submodule E S.V := orth S U
  have hfU : ∀ a, F.fvec a ∈ U := fun a => Submodule.subset_span ⟨Sum.inl a, rfl⟩
  have hpU : ∀ b, P.fvec b ∈ U := fun b => Submodule.subset_span ⟨Sum.inr b, rfl⟩
  have hXU : F.X ≤ U := by
    unfold FlagG.X
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← fvecC F i]
    exact hfU _
  have hW : ∀ w ∈ W, ∀ u ∈ U, S.hT u w = 0 := fun w hw u hu =>
    (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hw u hu
  have hW' : ∀ w ∈ W, ∀ u ∈ U, S.hT w u = 0 := fun w hw u hu => by
    rw [hsw, hW w hw u hu, star_zero]

  have hgram : ∀ i j, S.hT (tg i) (tg j) = S.hT (b₂ i) (b₂ j) := by
    have hz : ∀ a c, S.hT (F.fvec a) (Q.fvec c) = S.hT (F.fvec a) (P.fvec c) := fun a c => by
      have h := congrFun (congrFun hZ a) c
      simp only [Zhat, brS] at h
      exact h.symm
    rintro (a | a) (c | c)
    · rfl
    · exact hz a c
    · show S.hT (Q.fvec a) (F.fvec c) = S.hT (P.fvec a) (F.fvec c)
      rw [hsw S (F.fvec c), hsw S (F.fvec c), hz]
    · exact gram_flag P Q a c

  have hsplit : ∀ (g : Fin (r + 1) ⊕ Fin (r + 1) → E),
      ∑ i, g i • b₂ i = ∑ a, g (Sum.inl a) • F.fvec a + ∑ b, g (Sum.inr b) • P.fvec b := fun g => by
    rw [Fintype.sum_sum_type]; rfl
  have hLI : LinearIndependent E b₂ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F P (fun a => g (Sum.inl a)) (fun b => g (Sum.inr b)) 0
      (by rw [← hsplit, hg]) (fun _ => by simp) (fun _ => by simp) hGP
    rcases i with a | b
    · exact congrFun h.1 a
    · exact congrFun h.2 b
  have hdisj : Disjoint U W := by
    rw [Submodule.disjoint_def]
    intro v hv hvW
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
    have h := PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F P (fun a => g (Sum.inl a)) (fun b => g (Sum.inr b))
      (∑ i, g i • b₂ i) (hsplit g) (fun a => hW _ hvW _ (hfU a)) (fun b => hW _ hvW _ (hpU b)) hGP
    have h1 : ∀ a, g (Sum.inl a) = 0 := fun a => congrFun h.1 a
    have h2 : ∀ b, g (Sum.inr b) = 0 := fun b => congrFun h.2 b
    rw [hsplit]
    simp [h1, h2]
  have hcompl : IsCompl U W := by
    refine (Submodule.isCompl_iff_disjoint U W ?_).2 hdisj
    have h : finrank E W + finrank E U = finrank E S.V := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S U
    omega
  have hdec : ∀ v : S.V, ∃ g : Fin (r + 1) ⊕ Fin (r + 1) → E, ∃ w ∈ W, v = ∑ i, g i • b₂ i + w := by
    intro v
    have hv : v ∈ U ⊔ W := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
    exact ⟨g, w, hw, rfl⟩

  let K : (Fin (r + 1) → E) →ₗ[E] (Fin r → E) :=
    { toFun := fun c a => S.hT (F.e a) (∑ b, c b • P.fvec b)
      map_add' := by
        intro c c'
        funext a
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
      map_smul' := by
        intro m c
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, RingHom.id_apply] }
  obtain ⟨k, hkK, hk0⟩ := Submodule.ne_bot_iff _ |>.1 (LinearMap.ker_ne_bot_of_finrank_lt (f := K)
    (by simp))
  have hk : ∀ a, S.hT (F.e a) (∑ b, k b • P.fvec b) = 0 := fun a => congrFun (LinearMap.mem_ker.1 hkK) a
  have hx0 := hom k hk

  let A : F.X →ₗ[E] (Fin (r + 1) → E) := LinearMap.pi fun b => (S.hT (Q.fvec b)).comp F.X.subtype
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    exact PI.ScalarPairDr.W.eq_zero_of_orth F Q hG x.2 (fun b => congrFun hx b)
  let ℓ : (Fin (r + 1) → E) →ₗ[E] E := ∑ b, star (k b) • LinearMap.proj b
  have hℓ : ∀ t, ℓ t = ∑ b, star (k b) * t b := fun t => by
    simp [ℓ, LinearMap.sum_apply]
  have hℓcomb : ∀ (x : Fin (r + 1) → S.V) (y : S.V),
      ℓ (fun b => S.hT (x b) y) = S.hT (∑ b, k b • x b) y := fun x y => by
    rw [hℓ, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun b _ => (hT_smulL S _ _ _).symm
  have hrange : LinearMap.range A = LinearMap.ker ℓ := by
    have hle : LinearMap.range A ≤ LinearMap.ker ℓ := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      have e1 : (A x) = fun b => S.hT (Q.fvec b) x := rfl
      rw [e1, hℓcomb]
      have e2 : ∑ b, k b • Q.fvec b = ∑ b, k b • P.fvec b + ∑ b, k b • (Q.fvec b - P.fvec b) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by rw [smul_sub]; abel
      rw [e2, map_add, LinearMap.add_apply, hT_X_X F hx0 x.2, add_zero, hsw,
        spanL S F.e _ hk _ x.2, star_zero]
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have h1 : finrank E (LinearMap.range A) = r := by
      rw [LinearMap.finrank_range_of_inj hAinj]
      unfold FlagG.X
      rw [finrank_span_eq_card F.e_indep, Fintype.card_fin]
    have h2 : LinearMap.ker ℓ ≠ ⊤ := by
      obtain ⟨b, hb⟩ := Function.ne_iff.1 hk0
      intro htop
      have : Pi.single b (1 : E) ∈ LinearMap.ker ℓ := by rw [htop]; trivial
      rw [LinearMap.mem_ker, hℓ] at this
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true] at this
      exact hb (by simpa using this)
    have h3 := Submodule.finrank_lt h2
    simp only [Module.finrank_fin_fun] at h3
    omega

  let tw : S.V →ₗ[E] (Fin (r + 1) → E) := LinearMap.pi fun b => S.hT (Q.fvec b - P.fvec b)
  have ht : ∀ w : W, tw w ∈ LinearMap.range A := by
    intro w
    rw [hrange, LinearMap.mem_ker]
    have e1 : tw w = fun b => S.hT (Q.fvec b - P.fvec b) (w : S.V) := rfl
    rw [e1, hℓcomb]
    exact hW _ w.2 _ (hXU hx0)
  let codR : W →ₗ[E] LinearMap.range A := (tw ∘ₗ W.subtype).codRestrict (LinearMap.range A) ht
  let xm : W →ₗ[E] F.X := (LinearEquiv.ofInjective A hAinj).symm.toLinearMap ∘ₗ codR
  have hxm : ∀ (w : W) b, S.hT (Q.fvec b) (xm w : S.V) = S.hT (Q.fvec b - P.fvec b) (w : S.V) := by
    intro w b
    have h := (LinearEquiv.ofInjective A hAinj).apply_symm_apply (codR w)
    have h2 : A (xm w) = tw w := by
      have := congrArg Subtype.val h
      rw [LinearEquiv.ofInjective_apply] at this
      exact this
    exact congrFun h2 b

  let bs := Basis.span hLI
  let Bm : U →ₗ[E] S.V := bs.constr E tg
  let ψ : W →ₗ[E] S.V := W.subtype - F.X.subtype ∘ₗ xm
  let n₀ : S.V →ₗ[E] S.V := LinearMap.ofIsCompl hcompl Bm ψ
  have hn₀b : ∀ i, n₀ (b₂ i) = tg i := by
    intro i
    have e : bs i = ⟨b₂ i, Submodule.subset_span ⟨i, rfl⟩⟩ := Basis.span_apply hLI i
    have := LinearMap.ofIsCompl_apply_left hcompl (φ := Bm) (ψ := ψ) (bs i)
    rw [e] at this
    rw [show b₂ i = ((⟨b₂ i, Submodule.subset_span ⟨i, rfl⟩⟩ : U) : S.V) from rfl, this, ← e]
    exact bs.constr_basis E tg i
  have hn₀w : ∀ (w : S.V) (hw : w ∈ W), n₀ w = w - (xm ⟨w, hw⟩ : S.V) := by
    intro w hw
    have := LinearMap.ofIsCompl_apply_right hcompl (φ := Bm) (ψ := ψ) ⟨w, hw⟩
    exact this
  have hn₀sum : ∀ g : Fin (r + 1) ⊕ Fin (r + 1) → E, n₀ (∑ i, g i • b₂ i) = ∑ i, g i • tg i := by
    intro g
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hn₀b]

  have hperp : ∀ (w : W) i, S.hT (tg i) ((w : S.V) - xm w) = 0 := by
    intro w i
    rcases i with a | b
    · show S.hT (F.fvec a) ((w : S.V) - xm w) = 0
      rw [map_sub, hW _ w.2 _ (hfU a), hT_f_X F a (xm w).2, sub_zero]
    · show S.hT (Q.fvec b) ((w : S.V) - xm w) = 0
      rw [map_sub, hxm, map_sub, LinearMap.sub_apply, hW _ w.2 _ (hpU b)]
      ring
  have hperpS : ∀ (w : W) (g : Fin (r + 1) ⊕ Fin (r + 1) → E),
      S.hT (∑ i, g i • tg i) ((w : S.V) - xm w) = 0 := fun w g =>
    spanL S tg _ (hperp w) _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hsumU : ∀ g : Fin (r + 1) ⊕ Fin (r + 1) → E, ∑ i, g i • b₂ i ∈ U := fun g =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hiso : ∀ x y, S.hT (n₀ x) (n₀ y) = S.hT x y := by
    intro v v'
    obtain ⟨g, w, hw, rfl⟩ := hdec v
    obtain ⟨g', w', hw', rfl⟩ := hdec v'
    rw [map_add n₀, map_add n₀, hn₀sum, hn₀sum, hn₀w w hw, hn₀w w' hw']
    set x := (xm ⟨w, hw⟩ : S.V)
    set x' := (xm ⟨w', hw'⟩ : S.V)
    have hx : x ∈ F.X := (xm ⟨w, hw⟩).2
    have hx' : x' ∈ F.X := (xm ⟨w', hw'⟩).2
    have e1 : S.hT (∑ i, g i • tg i) (w' - x') = 0 := hperpS ⟨w', hw'⟩ g
    have e2 : S.hT (w - x) (∑ i, g' i • tg i) = 0 := by rw [hsw, hperpS ⟨w, hw⟩ g', star_zero]
    have e3 : S.hT (w - x) (w' - x') = S.hT w w' := by
      have a1 := hW' w hw x' (hXU hx')
      have a2 := hW w' hw' x (hXU hx)
      have a3 := hT_X_X F hx hx'
      simp only [map_sub, LinearMap.sub_apply]
      rw [a1, a2, a3]
      ring
    have e4 : S.hT (∑ i, g i • b₂ i) w' = 0 := hW w' hw' _ (hsumU g)
    have e5 : S.hT w (∑ i, g' i • b₂ i) = 0 := hW' w hw _ (hsumU g')
    have e6 : S.hT (∑ i, g i • tg i) (∑ i, g' i • tg i) = S.hT (∑ i, g i • b₂ i) (∑ i, g' i • b₂ i) := by
      rw [hermitian_double_sum_expand, hermitian_double_sum_expand]
      simp only [hgram]
    simp only [map_add, LinearMap.add_apply]
    rw [e1, e2, e3, e4, e5, e6]
  have hinj : Function.Injective n₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact S.nondeg.1 v (fun y => by rw [← hiso v y, hv, map_zero, LinearMap.zero_apply])
  let n : S.V ≃ₗ[E] S.V := LinearEquiv.ofInjectiveEndo n₀ hinj
  have hn : ∀ x, n x = n₀ x := fun x => rfl
  refine ⟨n, fun x y => by rw [hn, hn, hiso], fun i => by rw [hn]; exact hn₀b (Sum.inl i),
    fun b => by rw [hn]; exact hn₀b (Sum.inr b), ?_⟩
  intro v hv
  obtain ⟨g, w, hw, rfl⟩ := hdec v
  have key : n (∑ i, g i • b₂ i + w) - (∑ i, g i • b₂ i + w) =
      ∑ b, g (Sum.inr b) • (Q.fvec b - P.fvec b) - (xm ⟨w, hw⟩ : S.V) := by
    rw [hn, map_add, hn₀sum, hn₀w w hw, hsplit]
    simp only [tg, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [key]
  refine Submodule.sub_mem _ (hom _ fun a => ?_) (xm ⟨w, hw⟩).2
  have heX : F.e a ∈ F.X := Submodule.subset_span ⟨a, rfl⟩
  have h1 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hv (F.e a) heX
  have hw0 : S.hT (F.e a) w = 0 := hW w hw (F.e a) (hXU heX)
  have h2 : S.hT (F.e a) (∑ a', g (Sum.inl a') • F.fvec a') = 0 :=
    spanR S F.fvec (F.e a) (fun c => by rw [hsw, hT_f_e, star_zero]) _
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [map_add, hw0, add_zero, hsplit, map_add, h2, zero_add] at h1
  exact h1

end NMoveP

open NMoveP in

theorem n_move_holds (D : Formalism.BasicNotions.D7) : NMove D := by
  intro T T' F0 F'₂ F' hZ hG hO
  obtain ⟨n, hiso, hf, hp, horth⟩ := exists_move (VS D) F0 F'₂.fl F'.fl hZ hG hO
  have hfe : ∀ a, n (F0.e a) = F0.e a := fun a => by rw [← fvecC F0 a]; exact hf _
  refine ⟨n, ⟨hiso, ?_, horth, hfe, by rw [← fvecL F0]; exact hf _⟩,
    fun a => by rw [← fvecC F'₂.fl a, ← fvecC F'.fl a]; exact hp _,
    by rw [← fvecL F'₂.fl, ← fvecL F'.fl]; exact hp _⟩
  intro j x hx
  have hle : Xflag (lf D F0) (j + 1) ≤ LinearMap.ker ((n : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id) := by
    show Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, _, rfl⟩
    simp [hfe]
  have h := hle hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h
  rw [show n x - x = 0 from h]
  exact Submodule.zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
