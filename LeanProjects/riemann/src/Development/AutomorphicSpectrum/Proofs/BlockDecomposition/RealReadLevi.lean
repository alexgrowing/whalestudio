import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFixedNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnCompactParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicElementBlockFormStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.CompanionTheory.ReadLevel

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ g ∈ K, ρ g v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

theorem extTensor_twRep {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (χ : G →* ℂˣ) (ψ : H →* ℂˣ)
    (m : G × H) (x : V ⊗[ℂ] W) :
    GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ) m x =
      ((χ m.1 * ψ m.2 : ℂˣ) : ℂ) • GlobalTheory.SmGL.extTensor ρ σ m x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v u =>
    rw [GlobalTheory.SmGL.extTensor_tmul, GlobalTheory.SmGL.extTensor_tmul, twRep_apply, twRep_apply,
      TensorProduct.smul_tmul_smul, Units.val_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem isSpherical_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {K : Subgroup G}
    (h : fixed σ K ≠ ⊥) : GlobalTheory.LGrp.IsSpherical ρ K := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine (Submodule.ne_bot_iff _).2 ⟨φ.toLinearEquiv.symm v, ?_, fun e => hv0 (by
    have h2 := congrArg φ.toLinearEquiv e
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2)⟩
  refine mem_fixed_iff.2 fun g hg => φ.toLinearEquiv.injective ?_
  have h1 : φ.toLinearEquiv (ρ g (φ.toLinearEquiv.symm v)) = σ g (φ.toLinearEquiv (φ.toLinearEquiv.symm v)) :=
    LinearMap.congr_fun (φ.isIntertwining' g) _
  rw [h1, LinearEquiv.apply_symm_apply]
  exact mem_fixed_iff.1 hv g hg

theorem fixed_ind₂_ne_bot (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin a) k × GL (Fin b) k) W) (K : Subgroup (GL (Fin n) k))
    (hK : IsOpen (K : Set (GL (Fin n) k))) (x : W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      ((GlobalTheory.SmGL.deltaHalf k (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p) : ℂˣ) : ℂ) •
        ρ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x) :
    fixed (GlobalTheory.SmGL.ind₂ e ρ) K ≠ ⊥ :=
  GlobalTheory.T.induced_fixed_nonzero _ _ _ _ K hK x hx hfix

theorem exists_fixed_of_sep {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G V} {S : Submodule ℂ V} {τ : Representation ℂ G X}
    (hs : Sep ρ S τ) {L : Subgroup G} (hL : IsOpen (L : Set G)) {v : V} (hv : v ∈ S) (hv0 : v ≠ 0)
    (hfix : v ∈ fixed ρ L) : ∃ x : X, x ≠ 0 ∧ ∀ m ∈ L, τ m x = x := by
  obtain ⟨-, J, Lj, hLj, hsep⟩ := hs
  have hsm : SmVec ρ v := ⟨L, hL, hfix⟩
  obtain ⟨j, hj⟩ : ∃ j, Lj j v ≠ 0 := by
    by_contra hc
    exact hv0 (hsep v hv hsm fun j => by_contra fun hj => hc ⟨j, hj⟩)
  refine ⟨Lj j v, hj, fun m hm => ?_⟩
  rw [← hLj j m v hv hsm, mem_fixed_iff.1 hfix m hm]

theorem fixed_ind₂_twist (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin a) k) V) (σ : Representation ℂ (GL (Fin b) k) W)
    (χ : GL (Fin a) k →* ℂˣ) (ψ : GL (Fin b) k →* ℂˣ)
    (K : Subgroup (GL (Fin n) k)) (hKo : IsOpen (K : Set (GL (Fin n) k))) (hKc : IsCompact (K : Set (GL (Fin n) k)))
    (x : V ⊗[ℂ] W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      GlobalTheory.SmGL.extTensor ρ σ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x ∧
      χ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).1 *
        ψ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).2 = 1) :
    fixed (GlobalTheory.SmGL.ind₂ e (GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ))) K ≠ ⊥ := by
  refine fixed_ind₂_ne_bot k e _ K hKo x hx fun p hp => ?_
  obtain ⟨h1, h2⟩ := hfix p hp
  rw [GlobalTheory.T.modulus_trivial_on_compact_parabolic k a b n e K hKc p hp, Units.val_one, one_smul, extTensor_twRep, h1, h2, Units.val_one, one_smul]

theorem isSpherical_of_join (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) U)
    (ρ : Representation ℂ (GL (Fin a) k) V) (σ : Representation ℂ (GL (Fin b) k) W)
    (χ : GL (Fin a) k →* ℂˣ) (ψ : GL (Fin b) k →* ℂˣ)
    (φ : π.Equiv (GlobalTheory.SmGL.ind₂ e (GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ))))
    (K : Subgroup (GL (Fin n) k)) (hKo : IsOpen (K : Set (GL (Fin n) k))) (hKc : IsCompact (K : Set (GL (Fin n) k)))
    (x : V ⊗[ℂ] W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      GlobalTheory.SmGL.extTensor ρ σ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x ∧
      χ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).1 *
        ψ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).2 = 1) :
    GlobalTheory.LGrp.IsSpherical π K :=
  isSpherical_of_equiv φ (fixed_ind₂_twist k e ρ σ χ ψ K hKo hKc x hx hfix)

theorem loc_pow {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (w : Pl E) (k : ℕ)
    (x : (w.adicCompletion E)ˣ) : (μ ^ k).loc w x = μ.loc w (x ^ k) := by
  rw [map_pow]
  induction k with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem twist_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (μ : HChar E) (w : Pl E)
    (m : GLw a w × GLw b w)
    (h : μ.loc w (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1) :
    (((μ ^ b).loc w).comp GeneralLinearGroup.det) m.1 * (((μ ^ a).loc w).comp GeneralLinearGroup.det) m.2 = 1 := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, loc_pow, loc_pow, ← map_mul, h]

theorem levi_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (K : Subgroup (GLw n w)) (Q : GLw a w × GLw b w → Prop) (hKQ : ∀ m X, blk h w m X ∈ K → Q m)
    (p : GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))) (hp : (p : GLw n w) ∈ K) :
    Q ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p)) := by
  obtain ⟨X, hX⟩ := GlobalTheory.T.parabolic_element_block_form E n a b h w p
  exact hKQ _ X (hX ▸ hp)

set_option maxHeartbeats 1000000 in
theorem rReadLev : RReadLev := by
  intro hR hJ E _ _ _ n a b h μ s₁ s₂ Pa Pb D c w K L G hKo hKc hLo hKL hG hG0 hGL
  obtain ⟨x, hx0, hx⟩ := exists_fixed_of_sep (hR E a b s₁ s₂ Pa Pb w c.g₁ c.g₂ c.u₁ c.u₂ c.t₁ c.t₂) hLo hG hG0 hGL
  obtain ⟨φ⟩ := hJ E n a b h (μ ^ b) (μ ^ a) Pa Pb D w c.join
  exact isSpherical_of_join (w.adicCompletion E) (GlobalTheory.SmGL.stdSum h) (lp D w) (lp Pa w) (lp Pb w)
    (((μ ^ b).loc w).comp GeneralLinearGroup.det) (((μ ^ a).loc w).comp GeneralLinearGroup.det)
    φ K hKo hKc x hx0 fun p hp =>
      have hq := levi_of_mem h w K _ hKL p hp
      ⟨hx _ hq.1, twist_eq_one μ w _ hq.2⟩

end GlobalTheory.CompanionTheory.ReadLevel
