import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapIntertwinesRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapInducedSurjectiveIntertwinerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentLeParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjUnipotentCharacterCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipotentLiftParabolicProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicIffMemEmbeddedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjEmbeddingCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDichotomyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddedSmallNeighbourhoodFactorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousParabolicProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentNormalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionCongrEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusParabolicProjFactorStatement

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

section AbsMain
variable {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem coinv_cInd (H U : Subgroup G) (hUH : U ≤ H) (hUn : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (hι : Continuous ι) (hstab : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (H' : Subgroup G') (hH' : ∀ x, x ∈ H' ↔ ι x ∈ H)
    (σ : Representation ℂ H W) (hσ : IsSmooth σ) (σ' : Representation ℂ H' W') (q : W →ₗ[ℂ] W')
    (hqs : Function.Surjective q)
    (hq : ∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w))
    (hker : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v})
    (hD : ∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1)
    (hcl : IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x})
    (hemb : ∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ')
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hcomp : ∃ K' ∈ 𝓝 (1 : G'), IsCompact K') :
    Nonempty ((twAct (cInd H σ) U θ ι hstab).Equiv (cInd H' σ')) := by
  classical
  have hex := GlobalTheory.T.quotient_map_intertwines_restriction H H' ι σ σ' q hι hH' hq hcl hemb hcomp
  choose T hT using hex
  have hext : ∀ F F' : cIndSpace H' σ', (∀ x, F.1.1.1 x = F'.1.1.1 x) → F = F' := fun F F' h =>
    Subtype.ext (Subtype.ext (Subtype.ext (funext h)))
  let Tl : cIndSpace H σ →ₗ[ℂ] cIndSpace H' σ' :=
    { toFun := T
      map_add' := fun a b => hext _ _ fun x => by
        rw [hT]
        show _ = (T a).1.1.1 x + (T b).1.1.1 x
        rw [hT, hT, ← map_add]
        rfl
      map_smul' := fun c a => hext _ _ fun x => by
        rw [hT]
        show _ = c • (T a).1.1.1 x
        rw [hT, ← map_smul]
        rfl }
  have hTl : ∀ f x, (Tl f).1.1.1 x = q (f.1.1.1 (ι x)) := hT
  have hkill : twKer (cInd H σ) U θ ≤ LinearMap.ker Tl := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, e, rfl⟩
    show Tl _ = 0
    refine hext _ _ fun x => ?_
    rw [hTl]
    obtain ⟨hv, hθ⟩ := hstab x u
    have hvH : ι x * (u : G) * (ι x)⁻¹ ∈ H := hUH hv
    have e1 : (cInd H σ (u : G) e - (θ u : ℂ) • e).1.1.1 (ι x) =
        σ ⟨_, hvH⟩ (e.1.1.1 (ι x)) - (θ ⟨_, hv⟩ : ℂ) • e.1.1.1 (ι x) := by
      rw [hθ]
      show e.1.1.1 (ι x * (u : G)) - (θ u : ℂ) • e.1.1.1 (ι x) = _
      have e2 := e.1.1.2 ⟨_, hvH⟩ (ι x)
      have e3 : e.1.1.1 (ι x * (u : G)) = e.1.1.1 (ι x * (u : G) * (ι x)⁻¹ * ι x) := by
        congr 1; group
      rw [e3]
      exact congrArg (· - _) e2
    rw [e1]
    show _ = (0 : W')
    exact (hker _).2 (Submodule.subset_span ⟨⟨_, hv⟩, _, rfl⟩)
  let Tq := (twKer (cInd H σ) U θ).liftQ Tl hkill
  have hinj : Function.Injective Tq := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h0 : Tl f = 0 := hy
    refine (Submodule.Quotient.mk_eq_zero _).2 (GlobalTheory.T.jacquet_kernel_span_twisted_character H U hUH hUn θ ι hstab σ q hσ hker hD hbase f fun x => ?_)
    rw [← hTl, h0]
    rfl
  have hsurj : Function.Surjective Tq := by
    intro F
    obtain ⟨f, hf⟩ := GlobalTheory.T.quotient_map_induced_surjective_intertwiner H H' ι σ σ' q hι hσ hqs hH' hq hemb hbase F
    refine ⟨Submodule.Quotient.mk f, ?_⟩
    show Tl f = F
    exact hext _ _ fun x => by rw [hTl, hf]
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Tq ⟨hinj, hsurj⟩) fun y => ?_⟩
  refine LinearMap.ext fun z => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine hext _ _ fun x => ?_
  have e1 : (twAct (cInd H σ) U θ ι hstab y) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (cInd H σ (ι y) f) := rfl
  show (Tq (twAct (cInd H σ) U θ ι hstab y (Submodule.Quotient.mk f))).1.1.1 x =
    (Tq (Submodule.Quotient.mk f)).1.1.1 (x * y)
  rw [e1]
  show (Tl _).1.1.1 x = (Tl f).1.1.1 (x * y)
  rw [hTl, hTl, map_mul]
  rfl

end AbsMain

section PhiProd
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem phiMinus_prodGP (ψ : AddChar k Circle) (hψ1 : ψ ≠ 1) {m j : ℕ}
    (a : Representation ℂ (GL (Fin m) k) V) (b : Representation ℂ (Mir k (j + 1)) W)
    (ha : IsSmooth a) (hb : IsSmooth b) :
    Nonempty ((phiMinus k ψ (n := m + j) (prodGP a b)).Equiv (prodGP a (phiMinus k ψ b))) := by
  classical
  have hsm : IsSmooth ((extTensor a b).comp (gpProj k m (j + 1))) := by
    intro w
    exact (isSmooth_extTensor ha hb w).preimage (GlobalTheory.T.continuous_parabolic_proj k m (j + 1))
  have hUH : MirUin k (m + (j + 1)) ≤ MirabolicParabolic k m (j + 1) := GlobalTheory.T.mirabolic_unipotent_le_parabolic k m (j + 1)
  let q : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] (TwJacquet b (MirUin k (j + 1)) (mirChar k ψ j)) :=
    LinearMap.lTensor V (twKer b (MirUin k (j + 1)) (mirChar k ψ j)).mkQ
  have hqs : Function.Surjective q := LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  have hq : ∀ (h : MirabolicParabolic k m j) (hh : embedding₂ k (m + j) h ∈ MirabolicParabolic k m (j + 1)) (w : V ⊗[ℂ] W),
      q (((extTensor a b).comp (gpProj k m (j + 1))) ⟨embedding₂ k (m + j) h, hh⟩ w) =
        ((extTensor a (phiMinus k ψ b)).comp (gpProj k m j)) h (q w) := by
    intro h hh w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v w =>
      have e := GlobalTheory.T.parabolic_proj_embedding_compat k m j h hh
      show q (extTensor a b (gpProj k m (j + 1) ⟨_, hh⟩) (v ⊗ₜ w)) =
        extTensor a (phiMinus k ψ b) (gpProj k m j h) (q (v ⊗ₜ w))
      rw [e]
      simp only [q, LinearMap.lTensor_tmul, extTensor_tmul]
      rfl
  have hker : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : MirUin k (m + (j + 1))) (v : V ⊗[ℂ] W),
      y = ((extTensor a b).comp (gpProj k m (j + 1))) ⟨u, hUH u.2⟩ v - (mirChar k ψ (m + j) u : ℂ) • v} := by
    intro w
    constructor
    · intro hw
      have hex := lTensor_exact V (LinearMap.exact_subtype_mkQ
        (twKer b (MirUin k (j + 1)) (mirChar k ψ j))) (Submodule.mkQ_surjective _)
      obtain ⟨t, rfl⟩ := (hex w).1 hw
      clear hw
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
      | tmul v x =>
        obtain ⟨x, hx⟩ := x
        simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
        induction hx using Submodule.span_induction with
        | zero => simp
        | add x y _ _ hx hy =>
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hx hy
        | smul c x _ hx =>
          rw [TensorProduct.tmul_smul]
          exact Submodule.smul_mem _ c hx
        | mem x hx =>
          obtain ⟨n, w', rfl⟩ := hx
          obtain ⟨u, hh, e⟩ := GlobalTheory.T.exists_unipotent_lift_parabolic_proj k m j n
          obtain ⟨-, hv, hθ⟩ := GlobalTheory.T.parabolic_proj_unipotent_character_compat k ψ m j u hh
          refine Submodule.subset_span ⟨u, v ⊗ₜ w', ?_⟩
          have e2 : (⟨_, hv⟩ : MirUin k (j + 1)) = n := Subtype.ext (congrArg Prod.snd e)
          rw [e2] at hθ
          show _ = extTensor a b (gpProj k m (j + 1) ⟨u, hh⟩) (v ⊗ₜ w') - _
          rw [e, hθ, extTensor_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          simp
    · intro hw
      induction hw using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
      | mem x hx =>
        obtain ⟨u, y, rfl⟩ := hx
        obtain ⟨e1, hv, hθ⟩ := GlobalTheory.T.parabolic_proj_unipotent_character_compat k ψ m j u (hUH u.2)
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
          have := congrArg₂ (· + ·) hx hy
          simp only [add_zero, ← map_add] at this
          rw [← this]
          congr 1
          simp only [map_add, smul_add]
          abel
        | tmul v w =>
          show q (extTensor a b (gpProj k m (j + 1) ⟨u, hUH u.2⟩) (v ⊗ₜ w) - _) = 0
          rw [extTensor_tmul, e1, ← hθ, map_one, Module.End.one_apply, map_sub, map_smul]
          simp only [q, LinearMap.lTensor_tmul]
          rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub, ← map_smul, ← map_sub]
          have : (twKer b (MirUin k (j + 1)) (mirChar k ψ j)).mkQ
              (b (gpProj k m (j + 1) ⟨u, hUH u.2⟩).2 w - (mirChar k ψ j ⟨_, hv⟩ : ℂ) • w) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Submodule.subset_span ⟨⟨_, hv⟩, w, rfl⟩
          rw [this, TensorProduct.tmul_zero]
  refine coinv_cInd (MirabolicParabolic k m (j + 1)) (MirUin k (m + (j + 1))) hUH (GlobalTheory.T.mirabolic_unipotent_normal k _) (mirChar k ψ (m + j))
    (embedding₂ k (m + j)) (GlobalTheory.T.continuous_mirabolic_embedding k _) (levi_stab ψ (m + j)) (MirabolicParabolic k m j) (GlobalTheory.T.mem_parabolic_iff_mem_embedded k m j)
    ((extTensor a b).comp (gpProj k m (j + 1))) hsm ((extTensor a (phiMinus k ψ b)).comp (gpProj k m j)) q
    hqs hq hker ?_ (GlobalTheory.T.isClosed_parabolic_mul_embedded_mirabolic k m j) (GlobalTheory.T.embedded_small_neighbourhood_factor k m j) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) ?_
  · intro g
    rcases GlobalTheory.T.mirabolic_double_coset_dichotomy k ψ hψ1 m j g with h | ⟨u, hx, h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨u, hx, fun w => ?_, h2⟩
      simp [h1]
  · obtain ⟨K, hKo, hKc, -⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k (m + j) Set.univ Filter.univ_mem
    exact ⟨K, hKo.mem_nhds (one_mem K), hKc⟩

end PhiProd

section Final

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def twistEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') (χ : G →* ℂˣ) :
    (twist ρ χ).Equiv (twist ρ' χ) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => by
    refine LinearMap.ext fun v => ?_
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    show e.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • ρ' g (e.toLinearEquiv v)
    rw [map_smul]
    exact congrArg _ h

def extEquiv {G₁ G₂ M V V' W W' : Type} [Group G₁] [Group G₂] [Group M] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {a : Representation ℂ G₁ V} {a' : Representation ℂ G₁ V'} {b : Representation ℂ G₂ W}
    {b' : Representation ℂ G₂ W'} (e : a.Equiv a') (f : b.Equiv b') (s : M →* G₁ × G₂) :
    Representation.Equiv ((extTensor a b).comp s) ((extTensor a' b').comp s) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) fun g => by
    refine TensorProduct.ext' fun v w => ?_
    have h1 := LinearMap.congr_fun (e.isIntertwining' (s g).1) v
    have h2 := LinearMap.congr_fun (f.isIntertwining' (s g).2) w
    show TensorProduct.congr e.toLinearEquiv f.toLinearEquiv (extTensor a b (s g) (v ⊗ₜ w)) =
      extTensor a' b' (s g) (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv (v ⊗ₜ w))
    rw [extTensor_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul, extTensor_tmul]
    exact congrArg₂ _ h1 h2

theorem isOpen_ker_dpowM (n : ℕ) (s : ℝ) :
    IsOpen (((dpowM (k := k) n s).ker : Subgroup (Mir k n)) : Set (Mir k n)) :=
  (isOpen_ker_dpow k (n + 1) s).preimage continuous_subtype_val

theorem prodGP_congr {m j : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {a : Representation ℂ (GL (Fin m) k) V} {a' : Representation ℂ (GL (Fin m) k) V'}
    {c : Representation ℂ (Mir k j) W} {c' : Representation ℂ (Mir k j) W'} (e : a.Equiv a') (f : c.Equiv c') :
    Nonempty ((prodGP a c).Equiv (prodGP a' c')) :=
  GlobalTheory.T.compactInduction_congr_equiv (MirabolicParabolic k m j) _ _ (extEquiv e f (gpProj k m j))

theorem tw_rep {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (a : Representation ℂ (GL (Fin m) k) V) (c : Representation ℂ (Mir k j) W) (r : ℝ) :
    twist ((extTensor a c).comp (gpProj k m j)) ((dpowM (m + j) r).comp (MirabolicParabolic k m j).subtype) =
      (extTensor (twist a (dpow m r)) (twist c (dpowM j r))).comp (gpProj k m j) := by
  refine MonoidHom.ext fun h => LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v w =>
    show (dpowM (m + j) r (h : Mir k (m + j)) : ℂ) • extTensor a c (gpProj k m j h) (v ⊗ₜ w) =
      extTensor (twist a (dpow m r)) (twist c (dpowM j r)) (gpProj k m j h) (v ⊗ₜ w)
    rw [extTensor_tmul, extTensor_tmul, twist_apply, twist_apply, GlobalTheory.T.modulus_parabolic_proj_factor k m j r h, Units.val_mul,
      TensorProduct.smul_tmul_smul]

theorem cInd_of_eq {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) {σ σ' : Representation ℂ H W} (h : σ = σ') : Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  subst h; exact ⟨Representation.Equiv.refl _⟩

theorem twist_prodGP {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (a : Representation ℂ (GL (Fin m) k) V) (c : Representation ℂ (Mir k j) W) (r : ℝ) :
    Nonempty ((twist (prodGP a c) (dpowM (m + j) r)).Equiv (prodGP (twist a (dpow m r)) (twist c (dpowM j r)))) := by
  have A2 := GlobalTheory.T.compactInduction_twist_equiv (MirabolicParabolic k m j) ((extTensor a c).comp (gpProj k m j)) (dpowM (m + j) r) (isOpen_ker_dpowM _ _)
  have B := cInd_of_eq (MirabolicParabolic k m j) (tw_rep a c r)
  obtain ⟨A2⟩ := A2
  obtain ⟨B⟩ := B
  have C := A2.trans B
  unfold prodGP
  exact ⟨C⟩

def eqvOfEq {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ ρ' : Representation ℂ G V} (h : ρ = ρ') :
    ρ.Equiv ρ' := h ▸ Representation.Equiv.refl ρ

theorem main_twisted (ψ : AddChar k Circle) (hψ1 : ψ ≠ 1) {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin m) k) V)
    (τ : Representation ℂ (Mir k (j + 1)) W) (hρ : IsSmooth ρ) (hτ : IsSmooth τ) (s₀ s₁ t r : ℝ) (hs : r + s₀ = s₁) :
    Nonempty ((twist (phiMinus k ψ (n := m + j) (prodGP (twist ρ (dpow m s₀)) (twist τ (dpowM (j + 1) t))))
      (dpowM (m + j) r)).Equiv
      (prodGP (twist ρ (dpow m s₁)) (twist (twist (phiMinus k ψ τ) (dpowM j r)) (dpowM j t)))) := by
  have ha : IsSmooth (twist ρ (dpow (k := k) m s₀)) := isSmooth_twist hρ (isOpen_ker_dpow k m s₀)
  have hb : IsSmooth (twist τ (dpowM (k := k) (j + 1) t)) := isSmooth_twist hτ (isOpen_ker_dpowM _ _)
  have E0 := phiMinus_prodGP ψ hψ1 (twist ρ (dpow (k := k) m s₀)) (twist τ (dpowM (k := k) (j + 1) t)) ha hb
  have A2 := twist_prodGP (twist ρ (dpow (k := k) m s₀)) (phiMinus k ψ (twist τ (dpowM (k := k) (j + 1) t))) r
  obtain ⟨E0⟩ := E0
  obtain ⟨A2⟩ := A2
  have A4 : twist (twist ρ (dpow (k := k) m s₀)) (dpow m r) = twist ρ (dpow m s₁) := by
    rw [twist_twist, ← dpow_add, hs]
  have E3 := GlobalTheory.T.derivative_functor_twist_equiv k ψ j W τ t
  obtain ⟨E3⟩ := E3
  have A5 : (twist (twist (phiMinus k ψ τ) (dpowM j t)) (dpowM j r)) =
      twist (twist (phiMinus k ψ τ) (dpowM j r)) (dpowM j t) := by
    rw [twist_twist, twist_twist, mul_comm]
  have E5 := (twistEquiv E3 (dpowM j r)).trans (eqvOfEq A5)
  have E7 := prodGP_congr (eqvOfEq A4) E5
  obtain ⟨E7⟩ := E7
  exact ⟨(twistEquiv E0 _).trans (A2.trans E7)⟩

end Final

theorem phiGP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiGP k := by
  intro k _ _ _ _ ψ _ hψ1 m j ρ τ hρ hτ
  have X := main_twisted ψ hψ1 ρ.ρ τ.ρ hρ hτ (((j + 1 + 1 : ℕ) : ℝ) / 2) (((j + 1 : ℕ) : ℝ) / 2) (-((m : ℕ) : ℝ) / 2)
    (-1 / 2) (by push_cast; ring)
  unfold MIso
  have e : ∀ h : m + (j + 1) = m + j + 1, mcast h (prodGPn ρ τ) = prodGPn ρ τ := fun _ => rfl
  rw [e]
  unfold phiN prodGPn mtw MRep.phiM GRep.tw
  exact X

end GlobalTheory.CompanionTheory.LeibPhi

end
