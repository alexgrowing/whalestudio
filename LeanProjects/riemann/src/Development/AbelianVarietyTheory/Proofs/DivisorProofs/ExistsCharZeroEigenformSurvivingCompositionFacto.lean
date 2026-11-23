import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHeckeEigensystemDeligneSerreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFiniteFrameLatticeFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentFrameFormsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsToLatticeOfFiniteInvertibleStabilisersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastFrameCoeffRingNotDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylEqBotOfNotAntitoneStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.ExpFrame.Eigenform

theorem mem_of_ann {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (m : Ideal R) [m.IsPrime]
    (hne : ¬ Subsingleton (LocalizedModule m.primeCompl M)) (p : R) (hp : ∀ x : M, p • x = 0) : p ∈ m := by
  by_contra hpm
  apply hne
  have key : ∀ z : LocalizedModule m.primeCompl M, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h f s =>
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨p, hpm⟩, ?_⟩
      show (p : R) • ((s : R) • f) = (p : R) • ((s : R) • (0 : M))
      rw [smul_zero, smul_zero, hp]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem loc_subsingleton {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (S : Submonoid R)
    (h : ∀ x : M, x = 0) : Subsingleton (LocalizedModule S M) := by
  have key : ∀ z : LocalizedModule S M, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h f s => rw [h f, LocalizedModule.zero_mk]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem nabla_zero_of_not_antitone {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (τ0 : ι) (hτ0 : ¬ Antitone (res N (mu τ0))) : ∀ z : NablaT F.O N mu, z = 0 := by
  have hbot := GlobalTheory.T.dualWeyl_eq_bot_of_not_antitone' F.O N (res N (mu τ0)) hτ0
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : x τ0 = 0 :=
      Subtype.ext ((Submodule.eq_bot_iff _).1 hbot ((x τ0 : Formalism.GradedWeylDivisibility.dualWeyl F.O N N (res N (mu τ0))) : MvPolynomial _ F.O) (x τ0).2)
    rw [(PiTensorProduct.tprod F.O).map_coord_zero τ0 hx, smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem quot_ker_stable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (jKm : F.K →* alg F.O N mu) (ϖ : F.O) (κ : F.K) (x : NablaT F.O N mu)
    (hx : x ∈ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))) :
    repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu) κ x ∈ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)) := by
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)).map (repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu) κ) ≤
      (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨x, hx, rfl⟩

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Lift
variable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam mu : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) (jKm : F.K →* alg F.O N mu) (ϖ : F.O)
  (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm]
  [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)] [Module F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]

theorem hecke_compat (hH : F.IsHecke lam jK Gm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu))
    (π : NablaT F.O N mu →ₗ[F.O] (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))))
    (ψ : Gm →+ (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))))
    (hψs : ∀ (c : F.O) (w : Gm), ψ (c • w) = c • ψ w) (q : F.T)
    (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) (z : Forms F.O (A := alg F.O N lam) F.Γ jK Gm)
    (hxz : ∀ g, π ((x : F.G → NablaT F.O N mu) g) = ψ ((z : F.G → Gm) g)) (g : F.G) :
    π (((q • x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) : F.G → NablaT F.O N mu) g) =
      ψ (((q • z : Forms F.O (A := alg F.O N lam) F.Γ jK Gm) : F.G → Gm) g) := by
  induction q using MvPolynomial.induction_on generalizing x z g with
  | C c =>
    rw [hHm.1, hH.1]
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [map_smul, hxz, hψs]
  | add p q hp hq =>
    rw [add_smul, add_smul]
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    rw [hp x z hxz g, hq x z hxz g]
  | mul_X p i hp =>
    rw [mul_comm, mul_smul, mul_smul, hHm.2, hH.2, map_smul, hψs, map_sum, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => hp x z hxz (g * s)

theorem ann_lift (hOk : F.Ok) (hJ : F.IsJ lam jK) (hJm : F.IsJ mu jKm)
    (hH : F.IsHecke lam jK Gm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu)) (hE : Embeds F.O N lam mu ϖ Gm) (p : F.T)
    (hp : ∀ x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu), p • x = 0)
    (y : Forms F.O (A := alg F.O N lam) F.Γ jK Gm) : p • y = 0 := by
  obtain ⟨ψ, hψi, hψc, hψg, -⟩ := hE
  have hψs : ∀ (c : F.O) (w : Gm), ψ (c • w) = c • ψ w := by
    intro c w
    rw [← algebraMap_smul (alg F.O N lam) c w, hψc]
  obtain ⟨Fm, hFm, hFπ⟩ := GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers F.O F.G F.Γ F.K (NablaT F.O N mu)
      (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)))
      (repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu)) (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      (by
        intro κ x hx
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
        exact quot_ker_stable F mu jKm ϖ κ x hx)
      (fun g => ⟨(hOk.tame g).1, GlobalTheory.T.isUnit_natCast_frameCoeffRing_not_dvd l ι N F hOk _ (hOk.tame g).2⟩)
      (fun g => ψ ((y : F.G → Gm) g))
      (by
        intro γ g κ yy hyy
        have hy := y.2 γ g κ
        show ψ ((y : F.G → Gm) ((γ : F.G) * g * κ)) = _
        rw [hy]
        show ψ (jK κ⁻¹ • (y : F.G → Gm) g) = Submodule.mkQ _ (jKm κ⁻¹ • yy)
        rw [hJ κ⁻¹, hJm κ⁻¹, smul_assoc, hψs, hψg _ _ _ hyy, smul_assoc, Submodule.mkQ_apply,
          Submodule.Quotient.mk_smul]
        rfl)
  apply Subtype.ext
  funext g
  apply hψi
  have := hecke_compat F lam mu jK jKm ϖ Gm hH hHm (Submodule.mkQ _) ψ hψs p ⟨Fm, hFm⟩ y (fun g => hFπ g) g
  rw [hp] at this
  simp only [Submodule.coe_zero, Pi.zero_apply, map_zero] at this ⊢
  exact this.symm

end Lift

section Eig
variable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (mu : ι → ℕ → ℕ)
  (jKm : F.K →* alg F.O N mu)

theorem tf_forms (hOk : F.Ok) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) (hbi : Function.Injective b)
    (c : F.O) (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) (hcx : c • x = 0) : c = 0 ∨ x = 0 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  apply Subtype.ext
  funext g
  have h1 : c • (x : F.G → NablaT F.O N mu) g = 0 := by
    have := congrArg (fun y : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu) => (y : F.G → NablaT F.O N mu) g) hcx
    simpa using this
  have h2 : F.emb c • b ((x : F.G → NablaT F.O N mu) g) = 0 := by rw [← map_smulₛₗ, h1, map_zero]
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (hOk.ring.1 (h.trans (map_zero _).symm)) hc
  · exact hbi (h.trans (map_zero b).symm)

def jmap (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) :
    Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu) →ₛₗ[F.emb] (F.G → NablaT (PadicAlgCl l) N mu) where
  toFun x g := b ((x : F.G → NablaT F.O N mu) g)
  map_add' x y := by funext g; simp
  map_smul' c x := by funext g; simp [map_smulₛₗ]

def heckeQ (i : F.I) : (F.G → NablaT (PadicAlgCl l) N mu) →ₗ[PadicAlgCl l] (F.G → NablaT (PadicAlgCl l) N mu) where
  toFun h g := F.emb (F.cst i) • ∑ s ∈ F.tr i, h (g * s)
  map_add' h h' := by funext g; simp [Finset.sum_add_distrib, smul_add]
  map_smul' c h := by funext g; simp [Finset.smul_sum, smul_comm c]

theorem form_of_mem_span (hJm : F.IsJ mu jKm) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu)
    (hbg : ∀ g x, b (grp F.O N mu g x) = grp (PadicAlgCl l) N mu (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x))
    (w : F.G → NablaT (PadicAlgCl l) N mu) (hw : w ∈ Submodule.span (PadicAlgCl l) (Set.range (jmap F mu jKm b))) :
    F.IsForm mu w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    constructor
    · intro γ hγ g
      have hx := x.2 ⟨γ, hγ⟩ g 1
      show b ((x : F.G → NablaT F.O N mu) (γ * g)) = b ((x : F.G → NablaT F.O N mu) g)
      simp only [OneMemClass.coe_one, mul_one, inv_one, map_one] at hx
      rw [hx]
      rfl
    · intro κ g
      have hx := x.2 1 g κ
      simp only [OneMemClass.coe_one, one_mul] at hx
      show F.emb (F.chi κ) • grp (PadicAlgCl l) N mu _ (b ((x : F.G → NablaT F.O N mu) (g * κ))) =
        b ((x : F.G → NablaT F.O N mu) g)
      rw [← hbg, ← map_smulₛₗ, hx]
      congr 1
      show (F.chi κ : F.O) • grp F.O N mu (F.kap κ) (jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g) = _
      have h2 : (F.chi κ : F.O) • grp F.O N mu (F.kap κ) (jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g) =
          jKm κ • jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g := by
        rw [hJm κ, smul_assoc]
        rfl
      rw [h2, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  | zero => exact ⟨fun _ _ _ => rfl, fun _ _ => by simp⟩
  | add w w' _ _ hw hw' =>
    refine ⟨fun γ hγ g => by simp [hw.1 γ hγ g, hw'.1 γ hγ g], fun κ g => ?_⟩
    simp only [Pi.add_apply, map_add, smul_add]
    rw [hw.2 κ g, hw'.2 κ g]
  | smul c w _ hw =>
    refine ⟨fun γ hγ g => by simp [hw.1 γ hγ g], fun κ g => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [smul_comm, hw.2 κ g]

variable [Module F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]
  [IsScalarTower F.O F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]

theorem jmap_equiv (hHm : F.IsHecke mu jKm (NablaT F.O N mu)) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu)
    (i : F.I) (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) :
    jmap F mu jKm b ((MvPolynomial.X i : F.T) • x) = heckeQ F mu i (jmap F mu jKm b x) := by
  funext g
  show b ((((MvPolynomial.X i : F.T) • x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) : F.G → NablaT F.O N mu) g) =
    F.emb (F.cst i) • ∑ s ∈ F.tr i, b ((x : F.G → NablaT F.O N mu) (g * s))
  rw [hHm.2 i x g, map_smulₛₗ, map_sum]

theorem eig_of_ann (hOk : F.Ok) (hJm : F.IsJ mu jKm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu))
    (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) (hbi : Function.Injective b)
    (hbg : ∀ g x, b (grp F.O N mu g x) = grp (PadicAlgCl l) N mu (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x))
    (hbli : ∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a))
    (m : Ideal F.T) [m.IsMaximal]
    (hannM : ∀ p : F.T, (∀ x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu), p • x = 0) → p ∈ m) :
    ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  have h1 := GlobalTheory.T.module_finite_frameLatticeForms l ι N F mu jKm hOk
  have h2 := tf_forms F mu jKm hOk b hbi
  have h3 := GlobalTheory.T.linearIndependent_frameForms_baseChange l ι N F mu jKm b hbi hOk hbli
  have h4 := jmap_equiv F mu jKm hHm b
  have h5 := @GlobalTheory.T.exists_integral_hecke_eigensystem_deligne_serre l _ F.O _ _ _ F.emb hOk.ring.1 hOk.ring.2 F.I (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) _ _ _ _ h1
  obtain ⟨θ, hθ1, hθ2, v, hvspan, hv0, hvT⟩ := h5 h2 (F.G → NablaT (PadicAlgCl l) N mu) (jmap F mu jKm b) (heckeQ F mu) h3 h4 m inferInstance hannM
  exact ⟨θ, ⟨v, hv0, form_of_mem_span F mu jKm hJm b hbg v hvspan, fun i g => congrFun (hvT i) g⟩, hθ1, hθ2⟩

end Eig

theorem eigenform_of_surviving : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (ϖ : F.O), F.Ok → F.IsJ lam jK → Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)], F.IsHecke lam jK Gm → Embeds F.O N lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal], ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)) → ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  intro l _ ι _ _ N F lam mu jK ϖ hOk hJ hϖ Gm _ _ _ _ _ hH hE m _ hne
  have hann := mem_of_ann m hne
  by_cases hdom : ∀ τ, Antitone (res N (mu τ))
  swap
  · exfalso
    push_neg at hdom
    obtain ⟨τ0, hτ0⟩ := hdom
    have h0 := nabla_zero_of_not_antitone F mu τ0 hτ0
    obtain ⟨ψ, hψi, -, -, -⟩ := hE
    have hG : ∀ a : Gm, a = 0 := by
      intro a
      apply hψi
      obtain ⟨ya, hya⟩ := Submodule.Quotient.mk_surjective _ (ψ a)
      rw [map_zero, ← hya, h0 ya, Submodule.Quotient.mk_zero]
    exact hne (loc_subsingleton _ fun f => Subtype.ext (funext fun g => hG _))
  obtain ⟨jKm, hJm⟩ := GlobalTheory.ExpFrame.levelMap_exists l ι N F mu
  obtain ⟨instT, instTS, hHm⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module l ι N F mu jKm hOk hJm (NablaT F.O N mu)
  obtain ⟨b, hbi, -, -, hbg, hbli, -⟩ := GlobalTheory.LatBC.baseChange_lattices l ι N F mu hOk.ring.1 hdom
  exact eig_of_ann F mu jKm hOk hJm hHm b hbi hbg hbli m
    (fun p hp => hann p (ann_lift F lam mu jK jKm ϖ Gm hOk hJ hJm hH hHm hE p hp))

end GlobalTheory.ExpFrame.Eigenform

end
