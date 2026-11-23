import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjOfNonSplit

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Formalism.MainNotions.StandardLattice Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.SplitProj

namespace GlobalTheory.SplitWeilDict

theorem lemB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hlam g hg h hh
  obtain ⟨o, ho⟩ := exists_extend (thetaSub ψ S T) Om
  have ho' : ∀ p f (hf : IsThetaFunO ψ S T f), o p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => ho p ⟨f, hf⟩
  have hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (o p f) := fun p f hf => by
    rw [ho' p f hf]
    exact (Om p ⟨f, hf⟩).2
  have hheis : ∀ (g' : GA D S) (k' : GA D T), g' ∈ GfC S → k' ∈ GfC T → ∀ u f, IsThetaFunO ψ S T f →
      o (g', k') (heisO ψ S T u f) = heisO ψ S T (actO S T g' k' u) (o (g', k') f) := by
    intro g' k' hg' hk' u f hf
    obtain ⟨f', h1, h2⟩ := hL.Heisenberg₂ hψ hg' hk' u ⟨f, hf⟩
    rw [ho' _ f hf, ← h2, ← h1]
    exact ho _ f'
  obtain ⟨c, hc, H⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (om (g, h) * o (g⁻¹, h⁻¹))
    (fun f hf => hW.om_pres _ _ (hpres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hheis _ _ (inv_mem hg) (inv_mem hh) u f hf,
        hW.om_heis _ _ _ _ (hpres _ _ hf), GlobalTheory.FinWeilForm.actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hpres _ _ hf), ho' _ f hf,
        hL.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, hf⟩])
  refine ⟨c, hc, fun f hf => ?_⟩
  have h1 := H _ (hpres (g, h) f hf)
  rw [Module.End.mul_apply, ← Module.End.mul_apply (o _), ← map_mul,
    show ((g⁻¹, h⁻¹) * (g, h) : GA D S × GA D T) = 1 from inv_mul_cancel (g, h), map_one,
    Module.End.one_apply] at h1
  rw [h1, ho' _ f hf]

theorem lemC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om →
    (∀ g ∈ GfC S, ∀ h ∈ GfC T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ)) →
    ∀ (ε : AE D) (hε : GlobalTheory.RatAut.IsHalfIdem D ε), ∃ ν : GA D S × GA D T →* Circle, Continuous ν ∧
      ∀ (p : GA D S × GA D T) f (hf : IsThetaFunO ψ S T f),
        om (GlobalTheory.SplitProj.proj hε S p.1, GlobalTheory.SplitProj.proj hε T p.2) f =
          (ν p : ℂ) • (Om (GlobalTheory.SplitProj.proj hε S p.1, GlobalTheory.SplitProj.proj hε T p.2) ⟨f, hf⟩ : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT hS hT w lam Om hL hB ε hε
  let P : GA D S × GA D T →* GA D S × GA D T := (proj hε S).prodMap (proj hε T)
  have hPc : Continuous P := (continuous_proj hε).prodMap (continuous_proj hε)
  have hs : ∀ p : GA D S × GA D T, ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f (hf : IsThetaFunO ψ S T f), om (P p) f = c • (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) :=
    fun p => hB _ (proj_mem_GfC hε p.1) _ (proj_mem_GfC hε p.2)
  choose c hc h using hs
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hne : ∀ p, (Om p ⟨f, hf⟩ : WO S T → ℂ) ≠ 0 := fun p h0 => f0 (by
    have h1 : Om p ⟨f, hf⟩ = 0 := Subtype.ext h0
    have h2 := congrArg (Om p⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at h2
    exact congrArg Subtype.val h2)
  refine ⟨MonoidHom.mk' (fun p => ⟨c p, mem_sphere_zero_iff_norm.2 (hc p)⟩) fun p q => Circle.ext ?_, ?_,
    fun p f hf => h p f hf⟩
  · show c (p * q) = c p * c q
    refine smul_left_injective ℂ (hne (P (p * q))) ?_
    show c (p * q) • (Om (P (p * q)) ⟨f, hf⟩ : WO S T → ℂ) = (c p * c q) • (Om (P (p * q)) ⟨f, hf⟩ : WO S T → ℂ)
    rw [← h _ f hf, map_mul P, map_mul om, Module.End.mul_apply, h q f hf, map_smul, h p _ (Om (P q) ⟨f, hf⟩).2,
      smul_smul, map_mul Om, Module.End.mul_apply, mul_comm (c q)]
  · refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun q => ?_) _
    obtain ⟨u, hu⟩ := Function.ne_iff.1 (hne (P q))
    have a1 : Continuous fun p => om (P p) f u := (hW.om_cont f hf u).comp hPc
    have a2 : Continuous fun p => (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) u := (hL.cont hS hT ⟨f, hf⟩ u).comp hPc
    refine ((a1.continuousAt).div a2.continuousAt hu).congr ?_
    filter_upwards [a2.continuousAt.eventually_ne hu] with p hp
    show om (P p) f u / (Om (P p) ⟨f, hf⟩ : WO S T → ℂ) u = c p
    rw [h p f hf, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hp]

theorem lemD : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (lam : ℕ →* ℂ) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
    GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om →
    (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
    ∀ e, IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
    ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ c : ℂ, ‖c‖ = 1 →
    (∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = c • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ)) →
    c = (splitFacO χS χT x y : ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hsq e he g h hg hh x y hx hy c hc H
  obtain ⟨r, hr, a⟩ := hW.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', b⟩ := hL.split hsq he hg hh
  obtain ⟨ℓ, hℓ, f₁, hf₁, h0⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ hψ S T e he
  have k := a ℓ hℓ f₁ hf₁
  rw [H f₁ hf₁, map_smul, b ℓ hℓ ⟨f₁, hf₁⟩, smul_eq_mul] at k
  have k1 : (c * (r' : ℂ)) * ℓ f₁ = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) * ℓ f₁ := by
    rw [mul_assoc]; exact k
  have k2 := mul_right_cancel₀ h0 k1
  have k3 := congrArg norm k2
  rw [norm_mul, norm_mul, hc, Circle.norm_coe, one_mul, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le] at k3
  rw [k3, mul_comm] at k2
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne') k2

theorem splitWeil_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
  (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
  IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ lam : ℕ →* ℂ, GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam →
  (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) →
  ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)),
  GlobalTheory.FinWeilO.IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε : AE D, GlobalTheory.RatAut.IsHalfIdem D ε →
  ∀ (g : GA D S) (h : GA D T), SuppAt ε S g → SuppAt ε T h → ∀ x y : (AE D)ˣ, IsDetAt ε S g x → IsDetAt ε T h y →
  ∀ f : GlobalTheory.FinWeilO.thetaSub ψ S T,
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • (Om (g, h) f : WO S T → ℂ) := by
  intro D ψ hψ S T χS χT om hW ΛS ΛT hS hT lam hlam hsq w Om hL ε hε g₀ h₀ hg₀ hh₀ x₀ y₀ hx₀ hy₀ f₀
  have hB := lemB D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hlam
  obtain ⟨ν, hνc, hν⟩ := lemC D ψ hψ S T χS χT om hW ΛS ΛT hS hT w lam Om hL hB ε hε
  obtain ⟨c, c1, c2, c3, c4, c5⟩ := GlobalTheory.FinWeilForm.exists_half_character hε S χT _ hW.hecT hW.resT
  obtain ⟨d, d1, d2, d3, d4, d5⟩ := GlobalTheory.FinWeilForm.exists_half_character hε T χS _ hW.hecS hW.resS
  obtain ⟨f₁, f1, hf₁⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hone : ∀ p : GA D S × GA D T, proj hε S p.1 = 1 → proj hε T p.2 = 1 → ν p = 1 := fun p a b => by
    have e := hν p f₁ hf₁
    rw [a, b, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one, map_one, Module.End.one_apply,
      Module.End.one_apply] at e
    exact Circle.ext (smul_left_injective ℂ f1 (e.symm.trans (one_smul ℂ f₁).symm))
  have hsp : ∀ e, IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h →
      ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ν (g, h) = splitFacO χS χT x y :=
    fun e he g h hg hh x y hx hy => by
      have e1 : ∀ f (hf : IsThetaFunO ψ S T f), om (g, h) f = (ν (g, h) : ℂ) • (Om (g, h) ⟨f, hf⟩ : WO S T → ℂ) :=
        fun f hf => by
          have := hν (g, h) f hf
          dsimp only at this
          rwa [proj_of_split hε he hg, proj_of_split hε he hh] at this
      exact Circle.ext (lemD D ψ hψ S T χS χT om hW ΛS ΛT w lam Om hL hsq e he g h hg hh x y hx hy _
        (Circle.norm_coe _) e1)
  have s1 : ∀ (V : HSp D) (a : AE D) i j, a * (Formalism.L2.Theta.mt V 1 - 1) i j = (Formalism.L2.Theta.mt V 1 - 1) i j :=
    fun V a i j => by rw [GlobalTheory.IdemSupport.mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have d1' : ∀ (V : HSp D) (e : AE D), IsDetAt e V 1 1 := fun V e => by
    show ((1 : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V 1).det + (1 - e)
    rw [GlobalTheory.IdemSupport.mt_one, Matrix.det_one, Units.val_one]
    ring
  let μ : GA D S × GA D T →* Circle := ν * (c.comp (MonoidHom.fst _ _)) * (d.comp (MonoidHom.snd _ _))⁻¹
  have hμ : ∀ p, μ p = ν p * c p.1 * (d p.2)⁻¹ := fun p => rfl
  have hμc : Continuous μ := by
    show Continuous fun p : GA D S × GA D T => ν p * c p.1 * (d p.2)⁻¹
    exact (hνc.mul (c1.comp continuous_fst)).mul (d1.comp continuous_snd).inv
  have hl := GlobalTheory.LocalGlobalChar.eq_one_of_local D S (μ.comp (MonoidHom.inl _ _)) (hμc.comp (Continuous.prodMk_left 1))
    (fun g hg => by
      show μ (g, 1) = 1
      rw [hμ, hone (g, 1) (proj_of_real hε hg) (map_one _), c2 g hg]
      simp)
    (fun e he g hg => by
      show μ (g, 1) = 1
      obtain ⟨x, hx⟩ := GlobalTheory.FinWeilForm.exists_isDetAt he S g
      rw [hμ, hsp e he g 1 hg (s1 T _) x 1 hx (d1' T e), c4 e he g hg x hx, splitFacO]
      simp)
    (fun v η hv g hg => by
      show μ (g, 1) = 1
      rw [hμ, hone (g, 1) (proj_of_nonSplit hε hv hg) (map_one _), c3 v η hv g hg]
      simp)
  have hr := GlobalTheory.LocalGlobalChar.eq_one_of_local D T (μ.comp (MonoidHom.inr _ _)) (hμc.comp (Continuous.prodMk_right 1))
    (fun h hh => by
      show μ (1, h) = 1
      rw [hμ, hone (1, h) (map_one _) (proj_of_real hε hh), d2 h hh]
      simp)
    (fun e he h hh => by
      show μ (1, h) = 1
      obtain ⟨y, hy⟩ := GlobalTheory.FinWeilForm.exists_isDetAt he T h
      rw [hμ, hsp e he 1 h (s1 S _) hh 1 y (d1' S e) hy, d4 e he h hh y hy, splitFacO]
      simp)
    (fun v η hv h hh => by
      show μ (1, h) = 1
      rw [hμ, hone (1, h) (map_one _) (proj_of_nonSplit hε hv hh), d3 v η hv h hh]
      simp)
  have hall : ∀ p, μ p = 1 := fun p => by
    have : p = (p.1, 1) * (1, p.2) := Prod.ext (mul_one _).symm (one_mul _).symm
    rw [this, map_mul, show μ (p.1, 1) = 1 from hl p.1, show μ (1, p.2) = 1 from hr p.2, mul_one]
  have hνp : ν (g₀, h₀) = splitFacO χS χT x₀ y₀ := by
    have h1 := hall (g₀, h₀)
    rw [hμ, mul_inv_eq_one] at h1
    rw [splitFacO, ← c5 g₀ x₀ hx₀, ← d5 h₀ y₀ hy₀, ← h1]
    show ν (g₀, h₀) = (c g₀)⁻¹ * (ν (g₀, h₀) * c g₀)
    rw [mul_comm, mul_inv_cancel_right]
  have e := hν (g₀, h₀) f₀.1 f₀.2
  dsimp only at e
  rw [proj_of_suppAt hε hg₀, proj_of_suppAt hε hh₀, hνp] at e
  exact e

end GlobalTheory.SplitWeilDict
