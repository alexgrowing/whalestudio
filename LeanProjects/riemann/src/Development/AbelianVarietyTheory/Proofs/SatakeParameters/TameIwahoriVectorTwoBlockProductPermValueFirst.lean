import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.TameIwahori.PermCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_val_le {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (h1 : ∀ i j, valuation k ((g : Matrix n n k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL n k) : Matrix n n k) i j) ≤ 1) : g ∈ KO k n :=
  (GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨h1, h2⟩

theorem permGL_mem_KO {N : ℕ} (w : Equiv.Perm (Fin N)) : GlobalTheory.Parabolic.permGL k w ∈ KO k (Fin N) := by
  have key : ∀ v : Equiv.Perm (Fin N), ∀ i j,
      valuation k (((GlobalTheory.Parabolic.permGL k v : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
    intro v i j
    rw [GlobalTheory.Parabolic.permGL_apply]
    split_ifs <;> simp
  exact mem_KO_of_val_le (key w) (by rw [← map_inv]; exact key w⁻¹)

theorem val_det_of_mem_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k} (hg : g ∈ KO k m) :
    valuation k (GeneralLinearGroup.det g : k) = 1 := by
  obtain ⟨g, rfl⟩ := hg
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem emb₂_one_apply {r t : ℕ} (m : GL (Fin r) k) (x y : Fin r ⊕ Fin t) :
    ((emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) : GL (Fin (r + t)) k) : Matrix (Fin (r + t)) (Fin (r + t)) k)
      (stdSum rfl x) (stdSum rfl y) = fromBlocks (m : Matrix (Fin r) (Fin r) k) 0 0 1 x y := by
  rw [val_emb₂]
  simp

theorem emb₂_one_mem_KO {r t : ℕ} {m : GL (Fin r) k} (hm : m ∈ KO k (Fin r)) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) ∈ KO k (Fin (r + t)) := by
  have key : ∀ g : GL (Fin r) k, g ∈ KO k (Fin r) → ∀ i j, valuation k
      (((emb₂ k (stdSum (rfl : r + t = r + t)) (g, 1) : GL (Fin (r + t)) k) :
        Matrix (Fin (r + t)) (Fin (r + t)) k) i j) ≤ 1 := by
    intro g hg i j
    obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective i
    obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective j
    rw [emb₂_one_apply]
    have hg1 := ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1
    rcases x with a | a <;> rcases y with b | b
    · exact hg1 a b
    · simp
    · simp
    · rw [fromBlocks_apply₂₂, one_apply]
      split_ifs <;> simp
  refine mem_KO_of_val_le (key m hm) ?_
  have : (emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1))⁻¹ = emb₂ k (stdSum (rfl : r + t = r + t)) (m⁻¹, 1) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  rw [this]
  exact key _ (inv_mem hm)

theorem conj_apply {N : ℕ} (w : Equiv.Perm (Fin N)) (X : GL (Fin N) k) (p q : Fin N) :
    (((GlobalTheory.Parabolic.permGL k w)⁻¹ * X * GlobalTheory.Parabolic.permGL k w : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) p q = (X : Matrix (Fin N) (Fin N) k) (w p) (w q) := by
  have h := GlobalTheory.Parabolic.conj_permGL_apply (k := k) w⁻¹ X (w p) (w q)
  rw [map_inv, inv_inv] at h
  simpa using h

end GlobalTheory.TameIwahori.PermCell

namespace GlobalTheory.TameIwahori.PermCell

theorem exists_isIwVec_fst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (θ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V)
    (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _) (w : Equiv.Perm (Fin (r + t))),
    IsIwVec θ (prod₂ σ₁ σ₂) f → f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 →
    ∃ (s : Equiv.Perm (Fin r)) (y : V), y ≠ 0 ∧
      IsIwVec (fun i => θ (w.symm (Fin.castAdd t (s i)))) σ₁ y := by
  intro k _ _ _ _ r t θ V _ _ W _ _ σ₁ σ₂ f w hf hx
  classical
  have he : ∀ i : Fin r, stdSum (rfl : r + t = r + t) (Sum.inl i) = Fin.castAdd t i :=
    fun i => Fin.ext (by simp)
  have hPK := permGL_mem_KO (k := k) w

  have law : ∀ (q : parab k (two (stdSum (rfl : r + t = r + t)))) (g : GL (Fin (r + t)) k),
      f.1.1 ((q : GL (Fin (r + t)) k) * g) =
        Stages.dat (stdSum (rfl : r + t = r + t)) (extTensor σ₁ σ₂) q (f.1.1 g) := fun q g => f.1.2 q g
  have step : ∀ m : GL (Fin r) k, m ∈ KO k (Fin r) →
      f.1.1 (emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) * GlobalTheory.Parabolic.permGL k w) =
        LinearMap.rTensor W (σ₁ m) (f.1.1 (GlobalTheory.Parabolic.permGL k w)) := by
    intro m hm
    have h := law (Stages.sec (stdSum (rfl : r + t = r + t)) (m, 1)) (GlobalTheory.Parabolic.permGL k w)
    rw [Stages.dat_apply, Stages.dl_apply, Stages.pr_sec] at h
    have hv := val_det_of_mem_KO hm
    simp only [isUnram_absPow k _ _ hv, map_one, one_mul, Units.val_one, one_smul] at h
    refine h.trans ?_
    show TensorProduct.map (σ₁ m) (σ₂ 1) _ = _
    rw [map_one]
    rfl

  set s := Tuple.sort (fun i => w.symm (Fin.castAdd t i)) with hs
  have hmono : StrictMono (fun i => w.symm (Fin.castAdd t (s i))) :=
    (Tuple.monotone_sort (fun i => w.symm (Fin.castAdd t i))).strictMono_of_injective
      ((w.symm.injective.comp (Fin.castAdd_injective r t)).comp s.injective)
  have hSK := permGL_mem_KO (k := k) s
  have hSapp : ∀ (g : GL (Fin r) k) (i j : Fin r),
      ((GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹ : GL (Fin r) k) :
        Matrix (Fin r) (Fin r) k) (s i) (s j) = (g : Matrix (Fin r) (Fin r) k) i j :=
    fun g i j => GlobalTheory.Parabolic.conj_permGL_apply s g i j
  have hent : ∀ (m : GL (Fin r) k) (a b : Fin r ⊕ Fin t),
      (((GlobalTheory.Parabolic.permGL k w)⁻¹ * emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) *
          GlobalTheory.Parabolic.permGL k w : GL (Fin (r + t)) k) : Matrix (Fin (r + t)) (Fin (r + t)) k)
        (w.symm (stdSum rfl a)) (w.symm (stdSum rfl b)) =
        fromBlocks (m : Matrix (Fin r) (Fin r) k) 0 0 1 a b := by
    intro m a b
    rw [conj_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, emb₂_one_apply]
  have hsurj : ∀ p : Fin (r + t), ∃ a, w.symm (stdSum (rfl : r + t = r + t) a) = p :=
    fun p => ⟨(stdSum (rfl : r + t = r + t)).symm (w p), by simp⟩
  have hmove : ∀ m : GL (Fin r) k,
      emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) * GlobalTheory.Parabolic.permGL k w =
        GlobalTheory.Parabolic.permGL k w * ((GlobalTheory.Parabolic.permGL k w)⁻¹ *
          emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) * GlobalTheory.Parabolic.permGL k w) := by
    intro m; group

  have fix : ∀ g ∈ KO k (Fin r), (∀ i j, j < i → valuation k ((g : Matrix (Fin r) (Fin r) k) i j) < 1) →
      (∀ i, valuation k ((g : Matrix (Fin r) (Fin r) k) i i - 1) < 1) →
      LinearMap.rTensor W (σ₁ (GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹))
        (f.1.1 (GlobalTheory.Parabolic.permGL k w)) = f.1.1 (GlobalTheory.Parabolic.permGL k w) := by
    intro g hg hlow hdiag
    have hm : GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹ ∈ KO k (Fin r) :=
      mul_mem (mul_mem hSK hg) (inv_mem hSK)
    have hK := mul_mem (mul_mem (inv_mem hPK) (emb₂_one_mem_KO (t := t) hm)) hPK
    have h1 := hf.1 _ hK ?_ ?_
    · rw [← step _ hm, hmove]
      exact congrArg (fun F => F.1.1 (GlobalTheory.Parabolic.permGL k w)) h1
    · intro p q hpq
      obtain ⟨a, rfl⟩ := hsurj p
      obtain ⟨b, rfl⟩ := hsurj q
      rw [hent]
      rcases a with a | a <;> rcases b with b | b
      · obtain ⟨i, rfl⟩ := s.surjective a
        obtain ⟨j, rfl⟩ := s.surjective b
        rw [fromBlocks_apply₁₁, hSapp]
        rw [he, he] at hpq
        exact hlow i j (hmono.lt_iff_lt.1 hpq)
      · simp
      · simp
      · have hab : a ≠ b := by
          rintro rfl; exact lt_irrefl _ hpq
        rw [fromBlocks_apply₂₂, one_apply_ne hab]
        simp
    · intro p
      obtain ⟨a, rfl⟩ := hsurj p
      rw [hent]
      rcases a with a | a
      · obtain ⟨i, rfl⟩ := s.surjective a
        rw [fromBlocks_apply₁₁, hSapp]
        exact hdiag i
      · simp

  have tor : ∀ τ ∈ torusO k (Fin r),
      LinearMap.rTensor W (σ₁ (GlobalTheory.Parabolic.permGL k s * diagT k (Fin r) τ * (GlobalTheory.Parabolic.permGL k s)⁻¹))
        (f.1.1 (GlobalTheory.Parabolic.permGL k w)) =
        (torusChar (fun i => θ (w.symm (Fin.castAdd t (s i)))) τ : ℂ) • f.1.1 (GlobalTheory.Parabolic.permGL k w) := by
    intro τ hτ
    have hm : GlobalTheory.Parabolic.permGL k s * diagT k (Fin r) τ * (GlobalTheory.Parabolic.permGL k s)⁻¹ ∈ KO k (Fin r) :=
      mul_mem (mul_mem hSK (iwahori_le_KO k (Fin r) (diagT_mem_iwahori hτ))) (inv_mem hSK)
    let τ' : Fin (r + t) → kˣ := fun p =>
      Sum.elim (fun a => τ (s.symm a)) (fun _ => 1) ((stdSum (rfl : r + t = r + t)).symm (w p))
    have hτ'e : ∀ a, τ' (w.symm (stdSum (rfl : r + t = r + t) a)) = Sum.elim (fun a => τ (s.symm a)) (fun _ => 1) a :=
      fun a => by simp [τ']
    have hτ' : τ' ∈ torusO k (Fin (r + t)) := by
      intro p
      obtain ⟨a, rfl⟩ := hsurj p
      rw [hτ'e]
      rcases a with a | a
      · exact hτ _
      · simp
    have hh : (GlobalTheory.Parabolic.permGL k w)⁻¹ * emb₂ k (stdSum (rfl : r + t = r + t))
        (GlobalTheory.Parabolic.permGL k s * diagT k (Fin r) τ * (GlobalTheory.Parabolic.permGL k s)⁻¹, 1) *
          GlobalTheory.Parabolic.permGL k w = diagT k (Fin (r + t)) τ' := by
      ext p q
      obtain ⟨a, rfl⟩ := hsurj p
      obtain ⟨b, rfl⟩ := hsurj q
      rw [hent, val_diagT, diagonal_apply, hτ'e]
      rcases a with a | a <;> rcases b with b | b
      · obtain ⟨i, rfl⟩ := s.surjective a
        obtain ⟨j, rfl⟩ := s.surjective b
        rw [fromBlocks_apply₁₁, hSapp, val_diagT, diagonal_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg]
          intro h
          exact hij (s.injective (Sum.inl_injective ((stdSum (rfl : r + t = r + t)).injective
            (w.symm.injective h))))
      · simp
      · simp
      · rw [fromBlocks_apply₂₂, one_apply]
        by_cases hab : a = b
        · subst hab; simp
        · rw [if_neg hab, if_neg]
          intro h
          exact hab (Sum.inr_injective ((stdSum (rfl : r + t = r + t)).injective (w.symm.injective h)))
    have hc : torusChar θ τ' = torusChar (fun i => θ (w.symm (Fin.castAdd t (s i)))) τ := by
      rw [torusChar_apply, torusChar_apply]
      calc ∏ p, θ p (τ' p)
          = ∏ a : Fin r ⊕ Fin t, θ (w.symm (stdSum (rfl : r + t = r + t) a))
              (τ' (w.symm (stdSum (rfl : r + t = r + t) a))) :=
            (Equiv.prod_comp ((stdSum (rfl : r + t = r + t)).trans w.symm) (fun p => θ p (τ' p))).symm
        _ = ∏ a : Fin r, θ (w.symm (stdSum (rfl : r + t = r + t) (Sum.inl a))) (τ (s.symm a)) := by
            rw [Fintype.prod_sum_type]
            simp only [hτ'e, Sum.elim_inl, Sum.elim_inr, map_one, Finset.prod_const_one, mul_one]
        _ = ∏ i, θ (w.symm (Fin.castAdd t (s i))) (τ i) := by
            refine (Equiv.prod_comp s (fun a => θ (w.symm (stdSum (rfl : r + t = r + t) (Sum.inl a)))
              (τ (s.symm a)))).symm.trans ?_
            simp only [he, Equiv.symm_apply_apply]
    have h1 := hf.2 τ' hτ'
    rw [← hh] at h1
    rw [← step _ hm, hmove, ← hc]
    exact congrArg (fun F => F.1.1 (GlobalTheory.Parabolic.permGL k w)) h1

  let b := Module.Basis.ofVectorSpace ℂ W
  obtain ⟨i₀, hi₀⟩ : ∃ i, TensorProduct.equivFinsuppOfBasisRight b (f.1.1 (GlobalTheory.Parabolic.permGL k w)) i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((TensorProduct.equivFinsuppOfBasisRight b).map_eq_zero_iff.1 (Finsupp.ext h))
  set y₀ := TensorProduct.equivFinsuppOfBasisRight b (f.1.1 (GlobalTheory.Parabolic.permGL k w)) i₀ with hy₀
  have fix0 : ∀ g ∈ KO k (Fin r), (∀ i j, j < i → valuation k ((g : Matrix (Fin r) (Fin r) k) i j) < 1) →
      (∀ i, valuation k ((g : Matrix (Fin r) (Fin r) k) i i - 1) < 1) →
      σ₁ (GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹) y₀ = y₀ := by
    intro g hg hlow hdiag
    rw [hy₀, ← Stages.coord_rTensor, fix g hg hlow hdiag]
  have tor0 : ∀ τ ∈ torusO k (Fin r),
      σ₁ (GlobalTheory.Parabolic.permGL k s * diagT k (Fin r) τ * (GlobalTheory.Parabolic.permGL k s)⁻¹) y₀ =
        (torusChar (fun i => θ (w.symm (Fin.castAdd t (s i)))) τ : ℂ) • y₀ := by
    intro τ hτ
    rw [hy₀, ← Stages.coord_rTensor, tor τ hτ, map_smul, Finsupp.smul_apply]
  have hback : ∀ (g : GL (Fin r) k) (v : V), σ₁ g (σ₁ (GlobalTheory.Parabolic.permGL k s)⁻¹ v) =
      σ₁ (GlobalTheory.Parabolic.permGL k s)⁻¹
        (σ₁ (GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹) v) := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  refine ⟨s, σ₁ (GlobalTheory.Parabolic.permGL k s)⁻¹ y₀, ?_, ?_, ?_⟩
  · intro h0
    apply hi₀
    have := congrArg (σ₁ (GlobalTheory.Parabolic.permGL k s)) h0
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero,
      Module.End.one_apply] at this
  · intro g hg hlow hdiag
    rw [hback, fix0 g hg hlow hdiag]
  · intro τ hτ
    rw [hback, tor0 τ hτ, map_smul]

end GlobalTheory.TameIwahori.PermCell
