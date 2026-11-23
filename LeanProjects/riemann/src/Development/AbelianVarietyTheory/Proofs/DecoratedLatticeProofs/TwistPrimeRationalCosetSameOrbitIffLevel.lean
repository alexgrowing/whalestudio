import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)

noncomputable section
namespace GlobalTheory.TwBridge.LevOrb
open GlobalTheory.TwBridge.Lev

theorem inX_zero {E : Type} [Field E] (n : ℕ) (x : Fin n → E) : Loc.inX E n 0 x = x := by
  funext l
  simp [Loc.inX, show l.1 < n from l.2]

theorem mem_prX_zero {E : Type} [Field E] {n : ℕ} (J : Subgroup ((Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E)))
    (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : κ ∈ Loc.prX (Loc.Cbe J 1) ↔ (show (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E) from κ) ∈ J := by
  have hR : ∀ γ : (Fin (n + 0) → E) ≃ₗ[E] (Fin (n + 0) → E), Loc.R1cond E n 0 γ := fun γ => by
    rw [r1cond_iff]
    intro l l' h
    have := l.2
    have := l'.2
    omega
  constructor
  · rintro ⟨r, hr, hx⟩
    have h2 : r ∈ J := by simpa [MulAut.conj_apply] using hr.2
    have : r = κ := LinearEquiv.ext fun x => by simpa only [inX_zero] using hx x
    exact this ▸ h2
  · intro h
    refine ⟨κ, ⟨⟨hR _, hR _⟩, ?_⟩, fun x => by rw [inX_zero, inX_zero]⟩
    simpa [MulAut.conj_apply] using h

section Orb
variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}

omit [Fintype A] [DecidableEq A] in
theorem mem_box_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (M : ℕ) (v : Sp E n) :
    (fun r => ι (v (e r))) ∈ box A (ϖ ^ M) ↔ ((q : E) ^ M)⁻¹ • v ∈ stdAt E n P := by
  rw [stdAt, StabRef.mem_locStd, mem_box]
  have key : ∀ a : E, valuation k (ι a) ≤ valuation k ((ϖ ^ M : kˣ) : k) ↔ IntAt P (((q : E) ^ M)⁻¹ * a) := fun a => by
    rw [← hc.int, map_mul, map_inv₀, map_pow, ← hc.unif, Valuation.mem_integer_iff, map_mul, map_inv₀, Units.val_pow_eq_pow_val,
      inv_mul_le_iff₀ (zero_lt_iff.2 (by simp)), mul_one]
  refine ⟨fun h l => ?_, fun h r => (key _).2 (h (e r))⟩
  obtain ⟨r, rfl⟩ := e.surjective l
  exact (key _).1 (h r)

omit [NumberField E] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem phi_mulVec (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (z : Fin n → E) : (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) = fun r => ι (γ z (e r)) := by
  funext r
  rw [apply_sum γ z, map_sum, ← e.sum_comp]
  simp [mulVec, dotProduct, toBlocks₁₁, phi_val, toLoc, he]

theorem mulVec_mem_box {g : GL (A ⊕ Fin 0) k} (hg : g ∈ KO k _) (a : kˣ) {y : A → k} (hy : y ∈ box A a) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box A a := fun i => by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((mem_KO.1 hg).1 (Sum.inl i) (Sum.inl j)) (hy j)

theorem sameOrb_iff (hc : IsCompl P q ι ϖ) (e : A ≃ Fin n) (e' : A ⊕ Fin 0 ≃ Fin n) (he : ∀ a, e' (.inl a) = e a)
    (J : Subgroup (GL (A ⊕ Fin 0) k)) (h1 : KOne k _ ≤ J) (h2 : J ≤ KO k _) (M : ℕ) (z z' : Sp E n) :
    GlobalTheory.QPl.SameOrb J (box _ (ϖ ^ M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔
      ∃ γ : Sp E n ≃ₗ[E] Sp E n, phi ι e' γ ∈ J ∧ ((q : E) ^ M)⁻¹ • (γ z - z') ∈ stdAt E n P := by
  have hsub : ∀ γ : Sp E n ≃ₗ[E] Sp E n, (phi ι e' γ).val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) =
      fun r => ι ((γ z - z') (e r)) := fun γ => by
    rw [phi_mulVec e e' he]
    funext r
    simp
  constructor
  · rintro ⟨g, hg, y, hy, hy'⟩
    rw [Submodule.Quotient.eq] at hy hy'
    have h0 : g.val.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M) := by
      have := sub_mem hy' (mulVec_mem_box (h2 hg) _ hy)
      rw [mulVec_sub] at this
      convert this using 1
      abel
    have hU1 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k | MaxM ((g⁻¹).val * N - 1)} := by
      simp only [MaxM, Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact IsOpen.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => ((g⁻¹).val * N - 1) i j)
        (t := {z | valuation k z < 1}) (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
    have ho : IsOpen ((box A (ϖ ^ M) : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
      convert (isOpen_set_pi Set.finite_univ fun (_ : A) _ => isOpen_cball (ϖ ^ M)) using 1
      ext z; simp [mem_box, cball]
    have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r))) ∈ box A (ϖ ^ M)} := by
      refine ho.preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
        N.toBlocks₁₁ *ᵥ (fun r => ι (z (e r))) - (fun r => ι (z' (e r)))) ?_
      have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
        continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
      exact (hb.matrix_mulVec continuous_const).sub continuous_const
    obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense g.val (hU1.inter hU2) ⟨by
      change MaxM _
      rw [Units.inv_mul, sub_self]
      exact maxM_zero, h0⟩
    obtain ⟨u, hu, eu⟩ := exists_mem_KOne a1
    have ev : (g * u).val = M₀.map ι := by
      rw [Units.val_mul, eu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    obtain ⟨γ, hγ⟩ := exists_phi ι e' M₀ _ ev
    refine ⟨γ, hγ ▸ mul_mem hg (h1 hu), (mem_box_iff hc e M _).1 ?_⟩
    rw [← hsub, hγ, ev]
    exact a2
  · rintro ⟨γ, hγ, h⟩
    refine ⟨_, hγ, _, rfl, (Submodule.Quotient.eq _).2 ?_⟩
    rw [hsub]
    exact (mem_box_iff hc e M _).2 h

end Orb

theorem mem_prX_JQ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (hc : c = 0)
    (κ : Sp E n ≃ₗ[E] Sp E n) : κ ∈ Loc.prX (Loc.Cbe (LocE.JQ P q kj n c) 1) ↔
      (show Sp E (n + 0) ≃ₗ[E] Sp E (n + 0) from κ) ∈ LocE.JQ P q kj n 0 := by
  subst hc
  exact mem_prX_zero _ κ

theorem sameOrb_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W hA L G hL b hQ e he z z'
  have hc : cOf R (s + 1) = 0 := by have := hA.steps; unfold cOf; omega
  have hn : R.N (s + 1) = R.k + (s + 1) * (R.t + 1) := rfl
  let e' : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + 0) := (Equiv.sumEmpty _ _).trans e
  have he' : IsOrd (yPos xPos (R.N (s + 1))) e' := by
    rintro (a | a)
    · exact he a
    · exact a.elim0
  set o := stdOrd (Fin R.k) (Fin R.t) (s + 1) 0 (rfl : s + 1 + 0 = s + 1) with ho
  have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := fun g => by
    rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl,
      show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
    simp
  have hJ : ∀ g, g ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).J :=
    fun g => by rw [← hconj]; rfl
  have hmem : ∀ γ : Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Sp X.E (R.N (s + 1)), phi ι e' γ ∈ ((W.T s R).lev (s + 1) 0 rfl).J ↔
      γ ∈ prCat (Pr := Pr) cst.sharp (s + 1) P.1 (L.h (s + 1) b P) := fun γ => by
    rw [hJ, hL.last_h, prCat, Jat, if_neg hA.nmem, mem_prX_JQ _ _ _ _ _ hc]
    exact mem_par_iff (c := 0) (s := s) hA.compl W.unif rfl hn he' W.tame γ
  have hle : ((W.T s R).lev (s + 1) 0 rfl).J ≤ KO k _ := fun g hg => by
    have h := (mem_parahoric.1 ((hJ g).1 hg)).1
    rw [mem_KO] at h ⊢
    rw [← map_inv] at h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa [reGL_symm_val] using h.1 (o.symm i) (o.symm j)
    · simpa [reGL_symm_val] using h.2 (o.symm i) (o.symm j)
  rw [sameOrb_iff hA.compl e e' (fun _ => rfl) _
    (fun u hu => (hJ u).2 (((parahoric _ (Fin (s + 1) × Fin R.t) W.δ W.tame).reindex o).KOne_le hu)) hle, hL.grpQ]
  constructor
  · rintro ⟨γ, h1, h2⟩
    have h3 := (hmem γ).1 h1
    exact ⟨⟨γ, hL.int _ b P h3⟩, h3, h2⟩
  · rintro ⟨κ, h1, h2⟩
    exact ⟨κ.1, (hmem _).2 h1, h2⟩

end GlobalTheory.TwBridge.LevOrb
