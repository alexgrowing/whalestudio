import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicExtensionExactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiPreservesIsomorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductRankZeroTrivialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductLeftRankZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroLeftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionProductRankZeroRightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIsoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistProductDistributesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistTwistAddStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiltrationStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

namespace Main

section leaf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ses_of_mext {n : ℕ} {A B C : MRep k n} (h : MExt A B C) : Ses A.ρ B.ρ C.ρ := GlobalTheory.T.mirabolic_extension_exact k n A B C h
theorem miso_phiN (ψ : AddChar k Circle) {n : ℕ} {A B : MRep k (n + 1)} (h : MIso A B) : MIso (phiN ψ A) (phiN ψ B) :=
  GlobalTheory.T.phi_preserves_isomorphism k ψ n A B h
theorem giso_psiN {n : ℕ} {A B : MRep k n} (h : MIso A B) : GIso (psiN A) (psiN B) := GlobalTheory.T.psi_preserves_isomorphism k n A B h
theorem phi_gp_zero (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {m : ℕ} (ρ : GRep k (m + 1)) (τ : MRep k 0)
    (h : (m + 1) + 0 = (m + 0) + 1) (hρ : IsSmooth ρ.ρ) (hτ : IsSmooth τ.ρ) :
    Subsingleton (phiN ψ (mcast h (prodGPn ρ τ))).V := GlobalTheory.T.phi_product_rank_zero_trivial k ψ hc h1 m ρ τ h hρ hτ
theorem phi_product_trivial_right (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {i : ℕ} (τ : MRep k (i + 1)) (σ : GRep k 0)
    (h : (i + 1) + 0 = (i + 0) + 1) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) :
    MIso (phiN ψ (mcast h (prodPGn τ σ))) (prodPGn (phiN ψ τ) σ) := GlobalTheory.T.phi_product_left_rank_zero k ψ hc h1 i τ σ h hτ hσ
theorem restriction_product_left_trivial {j n : ℕ} (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n)
    (s₁ : IsSmooth π₁.ρ) (s₂ : IsSmooth π₂.ρ) :
    MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := GlobalTheory.T.restriction_product_rank_zero_left k j n π₁ π₂ h h' s₁ s₂
theorem restriction_product_right_trivial {i n : ℕ} (π₁ : GRep k (i + 1)) (π₂ : GRep k 0) (h : (i + 1) + 0 = n + 1) (h' : i + 0 = n)
    (s₁ : IsSmooth π₁.ρ) (s₂ : IsSmooth π₂.ρ) :
    MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodPGn (gres π₁) π₂)) := GlobalTheory.T.restriction_product_rank_zero_right k i n π₁ π₂ h h' s₁ s₂
theorem derivB_iso (ψ : AddChar k Circle) (j : ℕ) {n : ℕ} (π : GRep k (n + j)) :
    GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := GlobalTheory.T.derivative_twisted_iso k ψ j n π
theorem tw_prod {r t : ℕ} (A : GRep k r) (B : GRep k t) (s : ℝ) :
    GIso ((A.prod B).tw s) ((A.tw s).prod (B.tw s)) := GlobalTheory.T.twist_product_distributes k r t A B s
theorem tw_tw {n : ℕ} (A : GRep k n) (s s' : ℝ) : GIso ((A.tw s).tw s') (A.tw (s + s')) := GlobalTheory.T.twist_twist_add k n A s s'
theorem chain_filtration {n : ℕ} {R : ℕ → GRep k n → Prop} {Z : ℕ → Prop} {a b : ℕ} {X : GRep k n}
    (h : Chain R Z a b X) :
    ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧ F b = ⊥ ∧ ∀ i, a ≤ i → i < b →
      (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) :=
  GlobalTheory.T.exists_antitone_filtration_of_chain k n R Z a b X h
end leaf

section deriv
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_iterN (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {τ : MRep k (n + j)}, IsSmooth τ.ρ →
    IsSmooth (iterN ψ j τ).ρ
  | 0, _, _, h => h
  | j + 1, _, _, h => isSmooth_iterN ψ j (isSmooth_phiN ψ h)

theorem isSmooth_dN (ψ : AddChar k Circle) (j : ℕ) {n : ℕ} {τ : MRep k (n + j)} (h : IsSmooth τ.ρ) :
    IsSmooth (dN ψ j τ).ρ := isSmooth_psiN (isSmooth_iterN ψ j h)

theorem ses_iterN (ψ : AddChar k Circle) (hc : Continuous ψ) : ∀ (j : ℕ) {n : ℕ} {A B C : MRep k (n + j)},
    IsSmooth A.ρ → IsSmooth B.ρ → IsSmooth C.ρ → Ses A.ρ B.ρ C.ρ →
      Ses (iterN ψ j A).ρ (iterN ψ j B).ρ (iterN ψ j C).ρ
  | 0, _, _, _, _, _, _, _, h => h
  | j + 1, _, _, _, _, hA, hB, hC, h =>
    ses_iterN ψ hc j (isSmooth_phiN ψ hA) (isSmooth_phiN ψ hB) (isSmooth_phiN ψ hC) (ses_phiN ψ hc hA hB hC h)

theorem ses_dN (ψ : AddChar k Circle) (hc : Continuous ψ) (j : ℕ) {n : ℕ} {A B C : MRep k (n + j)}
    (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ) (hC : IsSmooth C.ρ) (h : Ses A.ρ B.ρ C.ρ) :
    Ses (dN ψ j A).ρ (dN ψ j B).ρ (dN ψ j C).ρ :=
  ses_psiN (isSmooth_iterN ψ j hA) (isSmooth_iterN ψ j hB) (isSmooth_iterN ψ j hC) (ses_iterN ψ hc j hA hB hC h)

theorem miso_iterN (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {A B : MRep k (n + j)}, MIso A B →
    MIso (iterN ψ j A) (iterN ψ j B)
  | 0, _, _, _, h => h
  | j + 1, _, _, _, h => miso_iterN ψ j (miso_phiN ψ h)

theorem giso_dN (ψ : AddChar k Circle) (j : ℕ) {n : ℕ} {A B : MRep k (n + j)} (h : MIso A B) :
    GIso (dN ψ j A) (dN ψ j B) := giso_psiN (miso_iterN ψ j h)

theorem subsingleton_phiN (ψ : AddChar k Circle) {n : ℕ} {A : MRep k (n + 1)} (h : Subsingleton A.V) :
    Subsingleton (phiN ψ A).V :=
  Function.Surjective.subsingleton (Submodule.mkQ_surjective (twKer A.ρ (MirUin k (n + 1)) (mirChar k ψ n)))

theorem subsingleton_iterN (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} {A : MRep k (n + j)}, Subsingleton A.V →
    Subsingleton (iterN ψ j A).V
  | 0, _, _, h => h
  | j + 1, _, _, h => subsingleton_iterN ψ j (subsingleton_phiN ψ h)

theorem subsingleton_psiN {n : ℕ} {A : MRep k n} (h : Subsingleton A.V) : Subsingleton (psiN A).V :=
  Function.Surjective.subsingleton (Submodule.mkQ_surjective (twKer A.ρ (MirUin k n) 1))

theorem subsingleton_dN (ψ : AddChar k Circle) (j : ℕ) {n : ℕ} {A : MRep k (n + j)} (h : Subsingleton A.V) :
    Subsingleton (dN ψ j A).V := subsingleton_psiN (subsingleton_iterN ψ j h)

theorem subsingleton_mcast {a b : ℕ} (e : a = b) {A : MRep k a} (h : Subsingleton A.V) : Subsingleton (mcast e A).V := by
  subst e; exact h

theorem phiN_mcast (ψ : AddChar k Circle) {a b c : ℕ} (X : MRep k a) (h : a = b + 1) (h2 : a = c + 1) (e : c = b) :
    phiN ψ (mcast h X) = mcast e (phiN ψ (mcast h2 X)) := by
  subst e; rfl

theorem mcast_mcast {a b c : ℕ} (e : a = b) (e' : b = c) (X : MRep k a) :
    mcast e' (mcast e X) = mcast (e.trans e') X := by
  subst e; subst e'; rfl

theorem ses_mcast {a b : ℕ} (e : a = b) {A B C : MRep k a} (h : Ses A.ρ B.ρ C.ρ) :
    Ses (mcast e A).ρ (mcast e B).ρ (mcast e C).ρ := by
  subst e; exact h

theorem isSmooth_gcast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : IsSmooth π.ρ) : IsSmooth (π.cast h).ρ := by
  subst h; exact hπ

theorem isSmooth_prod {r t : ℕ} (A : GRep k r) (B : GRep k t) : IsSmooth (A.prod B).ρ :=
  GlobalTheory.SmGL.isSmooth_parInd _ _

theorem gp_iso (hPsi : PsiGP k) (hPhi : PhiGP k) (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∀ (j n m : ℕ) (ρ : GRep k m) (τ : MRep k (n + j)) (N : ℕ) (hN : m + n = N) (h : m + (n + j) = N + j),
      IsSmooth ρ.ρ → IsSmooth τ.ρ → GIso (dN ψ j (mcast h (prodGPn ρ τ))) ((ρ.prod (dN ψ j τ)).cast hN) := by
  intro j
  induction j with
  | zero =>
    intro n m ρ τ N hN h hρ hτ
    subst hN
    exact hPsi m n ρ τ hρ hτ
  | succ j ih =>
    intro n m ρ τ N hN h hρ hτ
    subst hN
    have h2 : m + (n + (j + 1)) = (m + (n + j)) + 1 := by omega
    have e : m + (n + j) = (m + n) + j := by omega
    have s1 := hPhi ψ hc h1 m (n + j) ρ τ hρ hτ
    have s2 : MIso (phiN ψ (mcast h (prodGPn ρ τ))) (mcast e (prodGPn ρ (phiN ψ τ))) := by
      rw [phiN_mcast ψ _ h h2 e]
      exact miso_mcast e s1
    exact giso_trans (giso_dN ψ j s2) (ih n m ρ (phiN ψ τ) _ rfl e hρ (isSmooth_phiN ψ hτ))

theorem gp_zero (hPhi : PhiGP k) (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∀ (a j m n : ℕ) (ρ : GRep k m) (τ : MRep k a) (h : m + a = n + j), a < j → IsSmooth ρ.ρ → IsSmooth τ.ρ →
      Subsingleton (dN ψ j (mcast h (prodGPn ρ τ))).V := by
  intro a
  induction a with
  | zero =>
    intro j m n ρ τ h hj hρ hτ
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have e : m + 0 = n + j := by omega
    have h2 : (m + 1) + 0 = (m + 0) + 1 := by omega
    show Subsingleton (dN ψ j (phiN ψ (mcast h (prodGPn ρ τ)))).V
    rw [phiN_mcast ψ _ h h2 e]
    exact subsingleton_dN ψ j (subsingleton_mcast e (phi_gp_zero ψ hc h1 ρ τ h2 hρ hτ))
  | succ a ih =>
    intro j m n ρ τ h hj hρ hτ
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have e : m + a = n + j := by omega
    have h2 : m + (a + 1) = (m + a) + 1 := by omega
    have s1 := hPhi ψ hc h1 m a ρ τ hρ hτ
    have s2 : MIso (phiN ψ (mcast h (prodGPn ρ τ))) (mcast e (prodGPn ρ (phiN ψ τ))) := by
      rw [phiN_mcast ψ _ h h2 e]
      exact miso_mcast e s1
    have := ih j m n ρ (phiN ψ τ) e (by omega) hρ (isSmooth_phiN ψ hτ)
    exact subsingleton_of_giso (giso_symm (giso_dN ψ j s2))

theorem rp_shift (ψ : AddChar k Circle) {i t n j c : ℕ} (τ : MRep k (i + 1)) (σ : GRep k t) (A : GRep k n)
    (h : RP ψ (phiN ψ τ) σ j c A) : RP ψ τ σ (j + 1) (c + 1) A := by
  obtain ⟨b, d, i', t', rfl, hbd, hi, ht, hs, hA⟩ := h
  subst hi
  exact ⟨b + 1, d, i', t', rfl, by omega, rfl, ht, hs, hA⟩

theorem zp_shift {i t j c : ℕ} (h : ZP i t j c) : ZP (i + 1) t (j + 1) (c + 1) := by
  unfold ZP at *; omega

theorem top_gp (hPsi : PsiGP k) (hPhi : PhiGP k) (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    {i t n j : ℕ} (τ : MRep k i) (σ : GRep k (t + 1)) (e : i + t = n + j) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) :
    Top (RP ψ τ σ (j + 1)) (ZP i (t + 1) (j + 1)) 1 (dN ψ j (mcast e (prodGPn (psiN τ) (gres σ)))) := by
  by_cases hj : j ≤ t
  · obtain ⟨t, rfl⟩ : ∃ t', t = t' + j := ⟨t - j, by omega⟩
    have hN : i + t = n := by omega
    refine Or.inl ⟨_, ?_, gp_iso hPsi hPhi ψ hc h1 j t i (psiN τ) (gres σ) n hN e (isSmooth_psiN hτ) (isSmooth_gres hσ)⟩
    exact ⟨0, j + 1, i, t, rfl, by omega, rfl, rfl, hN, giso_refl _⟩
  · refine Or.inr ⟨?_, gp_zero hPhi ψ hc h1 t j i n (psiN τ) (gres σ) e (by omega) (isSmooth_psiN hτ) (isSmooth_gres hσ)⟩
    unfold ZP; omega

theorem pg_chain (hPsi : PsiGP k) (hPhi : PhiGP k) (hPsiPG : PsiPG k) (hPhiPG : PhiPG k) (hPhiPG0 : PhiPG0 k)
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∀ (j i t n : ℕ) (τ : MRep k i) (σ : GRep k t) (h : i + t = n + j), IsSmooth τ.ρ → IsSmooth σ.ρ →
      Chain (RP ψ τ σ j) (ZP i t j) 1 (j + 2) (dN ψ j (mcast h (prodPGn τ σ))) := by
  intro j
  induction j with
  | zero =>
    intro i t n τ σ h hτ hσ
    obtain rfl : n = i + t := by omega
    have := chain_top' (R := RP ψ τ σ 0) (Z := ZP i t 0) (a := 1) (X := dN ψ 0 (mcast h (prodPGn τ σ)))
      (Or.inl ⟨_, ⟨0, 0, i, t, rfl, rfl, rfl, rfl, rfl, giso_refl _⟩, hPsiPG i t τ σ hτ hσ⟩) 0 (by intro c; omega)
    exact this
  | succ j ih =>
    intro i t n τ σ h hτ hσ
    show Chain _ _ 1 (j + 1 + 2) (dN ψ j (phiN ψ (mcast h (prodPGn τ σ))))
    rcases i with _ | i <;> rcases t with _ | t
    · omega
    · have e : 0 + t = n + j := by omega
      have h2 : 0 + (t + 1) = (0 + t) + 1 := by omega
      have s2 : MIso (phiN ψ (mcast h (prodPGn τ σ))) (mcast e (prodGPn (psiN τ) (gres σ))) := by
        rw [phiN_mcast ψ _ h h2 e]
        exact miso_mcast e (hPhiPG0 ψ hc h1 t τ σ hσ)
      obtain ⟨e2⟩ := giso_dN ψ j s2
      refine chain_top (Y := zeroG n) (ses_zero_left e2) (top_gp hPsi hPhi ψ hc h1 τ σ e hτ hσ) ?_
      have := chain_zero (R := RP ψ τ σ (j + 1)) (Z := ZP 0 (t + 1) (j + 1)) (X := zeroG n) inferInstance (j + 1) 2
        (by intro c h3 _; unfold ZP; omega)
      rwa [show 2 + (j + 1) = j + 1 + 2 by omega] at this
    · have e : i + 0 = n + j := by omega
      have h2 : (i + 1) + 0 = (i + 0) + 1 := by omega
      have s2 : MIso (phiN ψ (mcast h (prodPGn τ σ))) (mcast e (prodPGn (phiN ψ τ) σ)) := by
        rw [phiN_mcast ψ _ h h2 e]
        exact miso_mcast e (phi_product_trivial_right ψ hc h1 τ σ h2 hτ hσ)
      have c1 := (ih i 0 n (phiN ψ τ) σ e (isSmooth_phiN ψ hτ) hσ).shift
        (R' := RP ψ τ σ (j + 1)) (Z' := ZP (i + 1) 0 (j + 1))
        (fun c A hA => rp_shift ψ τ σ A hA) (fun c hZ => zp_shift hZ)
      exact Chain.skip (by unfold ZP; omega) (giso_symm (giso_dN ψ j s2)) c1
    · have e : i + t + 1 = n + j := by omega
      have h2 : (i + 1) + (t + 1) = (i + t + 1) + 1 := by omega
      have ea : i + (t + 1) = n + j := by omega
      have eb : (i + 1) + t = n + j := by omega
      have ea' : i + (t + 1) = i + t + 1 := by omega
      have eb' : (i + 1) + t = i + t + 1 := by omega
      have hext := hPhiPG ψ hc h1 i t τ σ hτ hσ
      have ses0 := ses_mcast e (ses_of_mext hext)
      rw [mcast_mcast, mcast_mcast, ← phiN_mcast ψ _ h h2 e] at ses0
      have ses1 := ses_dN ψ hc j
        (isSmooth_mcast _ (isSmooth_prodPGn _ _)) (isSmooth_phiN ψ (isSmooth_mcast _ (isSmooth_prodPGn _ _)))
        (isSmooth_mcast _ (isSmooth_prodGPn _ _)) ses0
      have c1 := (ih i (t + 1) n (phiN ψ τ) σ ea (isSmooth_phiN ψ hτ) hσ).shift
        (R' := RP ψ τ σ (j + 1)) (Z' := ZP (i + 1) (t + 1) (j + 1))
        (fun c A hA => rp_shift ψ τ σ A hA) (fun c hZ => zp_shift hZ)
      exact chain_top ses1 (top_gp hPsi hPhi ψ hc h1 τ σ eb hτ hσ) c1

end deriv

section final
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rp_to_rf (ψ : AddChar k Circle) {r t n j a : ℕ} (π₁ : GRep k (r + 1)) (π₂ : GRep k t) (A : GRep k n)
    (h : RP ψ (gres π₁) π₂ j a A) : RF ψ π₁ π₂ (j + 1) a A := by
  obtain ⟨b, c, r', t', rfl, hbc, hi, ht, hs, hA⟩ := h
  subst hi
  exact ⟨c, r', t', by omega, rfl, ht, hs, hA⟩

theorem zp_to_zf {r t j a : ℕ} (h : ZP r t j a) : ZF (r + 1) t (j + 1) a := h

theorem main_chain (hRes : ResSeq k) (hPsi : PsiGP k) (hPhi : PhiGP k) (hPsiPG : PsiPG k) (hPhiPG : PhiPG k)
    (hPhiPG0 : PhiPG0 k) (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (ℓ r t n : ℕ) (hn : r + t = n + ℓ) (π₁ : GRep k r) (π₂ : GRep k t) (s₁ : IsSmooth π₁.ρ) (s₂ : IsSmooth π₂.ρ) :
    Chain (RF ψ π₁ π₂ ℓ) (ZF r t ℓ) 0 (ℓ + 1) (dG ψ ℓ ((π₁.prod π₂).cast hn)) := by
  cases ℓ with
  | zero =>
    obtain rfl : n = r + t := by omega
    have top : Top (RF ψ π₁ π₂ 0) (ZF r t 0) 0 ((π₁.prod π₂).cast hn) :=
      Or.inl ⟨_, ⟨0, r, t, rfl, rfl, rfl, rfl, giso_refl _⟩, giso_refl _⟩
    exact chain_top' top 0 (by intro c; omega)
  | succ j =>
    show Chain _ _ 0 (j + 1 + 1) (dN ψ j (gres ((π₁.prod π₂).cast hn)))
    rcases r with _ | r <;> rcases t with _ | t
    · omega
    · obtain rfl : t = n + j := by omega
      have e : 0 + (n + j) = n + j := by omega
      have s := restriction_product_left_trivial π₁ π₂ hn e s₁ s₂
      have top : Top (RF ψ π₁ π₂ (j + 1)) (ZF 0 (n + j + 1) (j + 1)) 0 (dN ψ j (gres ((π₁.prod π₂).cast hn))) := by
        refine Or.inl ⟨_, ?_, giso_trans (giso_dN ψ j s)
          (gp_iso hPsi hPhi ψ hc h1 j n 0 π₁ (gres π₂) n (by omega) e s₁ (isSmooth_gres s₂))⟩
        exact ⟨j + 1, 0, n, by omega, rfl, rfl, by omega, giso_refl _⟩
      have c2 := chain_top' top (j + 1) (by intro c h3 _; unfold ZF; omega)
      rwa [show 0 + 1 + (j + 1) = j + 1 + 1 by omega] at c2
    · have e : r + 0 = n + j := by omega
      have s := restriction_product_right_trivial π₁ π₂ hn e s₁ s₂
      have c1 := (pg_chain hPsi hPhi hPsiPG hPhiPG hPhiPG0 ψ hc h1 j r 0 n (gres π₁) π₂ e (isSmooth_gres s₁) s₂).mono
        (R' := RF ψ π₁ π₂ (j + 1)) (Z' := ZF (r + 1) 0 (j + 1))
        (fun c A hA => rp_to_rf ψ π₁ π₂ A hA) (fun c hZ => zp_to_zf hZ)
      exact Chain.skip (a := 0) (by unfold ZF; omega) (giso_symm (giso_dN ψ j s)) c1
    · have e0 : r + t + 1 = n + j := by omega
      have e1 : r + (t + 1) = n + j := by omega
      have e2 : (r + 1) + t = n + j := by omega
      have hx := hRes r t (n + j) e0 π₁ π₂ s₁ s₂
      have ses := ses_dN ψ hc j (isSmooth_mcast _ (isSmooth_prodPGn _ _))
        (isSmooth_gres (isSmooth_gcast _ (isSmooth_prod _ _))) (isSmooth_mcast _ (isSmooth_prodGPn _ _)) (ses_of_mext hx)
      have c1 := (pg_chain hPsi hPhi hPsiPG hPhiPG hPhiPG0 ψ hc h1 j r (t + 1) n (gres π₁) π₂ e1 (isSmooth_gres s₁) s₂).mono
        (R' := RF ψ π₁ π₂ (j + 1)) (Z' := ZF (r + 1) (t + 1) (j + 1))
        (fun c A hA => rp_to_rf ψ π₁ π₂ A hA) (fun c hZ => zp_to_zf hZ)
      have top : Top (RF ψ π₁ π₂ (j + 1)) (ZF (r + 1) (t + 1) (j + 1)) 0
          (dN ψ j (mcast e2 (prodGPn π₁ (gres π₂)))) := by
        by_cases hj : j ≤ t
        · obtain ⟨t, rfl⟩ : ∃ t', t = t' + j := ⟨t - j, by omega⟩
          have hN : r + 1 + t = n := by omega
          refine Or.inl ⟨_, ?_, gp_iso hPsi hPhi ψ hc h1 j t (r + 1) π₁ (gres π₂) n hN e2 s₁ (isSmooth_gres s₂)⟩
          exact ⟨j + 1, r + 1, t, by omega, rfl, rfl, hN, giso_refl _⟩
        · refine Or.inr ⟨?_, gp_zero hPhi ψ hc h1 t j (r + 1) n π₁ (gres π₂) e2 (by omega) s₁ (isSmooth_gres s₂)⟩
          unfold ZF; omega
      exact chain_top ses top c1

theorem step_iso (ψ : AddChar k Circle) {r' t' a c ℓ n : ℕ} (hac : a + c = ℓ) (B₁ : GRep k (r' + a))
    (B₂ : GRep k (t' + c)) (hs : r' + t' = n) :
    GIso ((((dG ψ a B₁).prod (dG ψ c B₂)).cast hs).tw ((ℓ : ℝ) / 2))
      ((((derivB ψ a B₁).tw ((c : ℝ) / 2)).prod ((derivB ψ c B₂).tw ((a : ℝ) / 2))).cast hs) := by
  refine giso_trans (tw_cast hs _ _) (giso_cast hs ?_)
  refine giso_trans (tw_prod _ _ _) (giso_prod ?_ ?_)
  · refine giso_symm (giso_trans (giso_tw _ (derivB_iso ψ a B₁)) (giso_trans (tw_tw _ _ _) ?_))
    have : (a : ℝ) / 2 + (c : ℝ) / 2 = (ℓ : ℝ) / 2 := by subst hac; push_cast; ring
    rw [this]; exact giso_refl _
  · refine giso_symm (giso_trans (giso_tw _ (derivB_iso ψ c B₂)) (giso_trans (tw_tw _ _ _) ?_))
    have : (c : ℝ) / 2 + (a : ℝ) / 2 = (ℓ : ℝ) / 2 := by subst hac; push_cast; ring
    rw [this]; exact giso_refl _

end final

theorem leibnizOrd_of_parts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ResSeq k → PsiGP k → PhiGP k → PsiPG k → PhiPG k → PhiPG0 k → LeibnizOrd k := by
  intro k _ _ _ _ hRes hPsi hPhi hPsiPG hPhiPG hPhiPG0 ψ hc h1 r t ℓ n hn π₁ π₂ s₁ s₂
  have c0 := main_chain hRes hPsi hPhi hPsiPG hPhiPG hPhiPG0 ψ hc h1 ℓ r t n hn π₁ π₂ s₁ s₂
  have c1 := (c0.tw ((ℓ : ℝ) / 2)).iso (giso_symm (derivB_iso ψ ℓ ((π₁.prod π₂).cast hn)))
  obtain ⟨F, hF, htop, hbot, hstep⟩ := chain_filtration c1
  refine ⟨F, hF, htop, hbot, fun i hi => ?_⟩
  have hs := hstep i (Nat.zero_le _) (by omega)
  split_ifs with hcond
  · rcases hs with ⟨A', ⟨A, ⟨c, r', t', hac, h₁, h₂, hsz, hA⟩, hA'⟩, hq⟩ | ⟨hZ, _⟩
    · obtain rfl : c = ℓ - i := by omega
      obtain rfl : r' = r - i := by omega
      obtain rfl : t' = t - (ℓ - i) := by omega
      refine ⟨hsz, ?_⟩
      obtain ⟨q⟩ := hq
      obtain ⟨e⟩ := giso_trans hA' (giso_trans (giso_tw _ hA) (step_iso ψ hac (π₁.cast h₁) (π₂.cast h₂) hsz))
      exact ⟨q.trans e⟩
    · exact absurd hcond hZ
  · rcases hs with ⟨A', ⟨A, ⟨c, r', t', hac, h₁, h₂, hsz, hA⟩, hA'⟩, hq⟩ | ⟨_, he⟩
    · exact absurd ⟨by omega, by omega⟩ hcond
    · exact he

end Main

end GlobalTheory.CompanionTheory.LeibOrd

end
