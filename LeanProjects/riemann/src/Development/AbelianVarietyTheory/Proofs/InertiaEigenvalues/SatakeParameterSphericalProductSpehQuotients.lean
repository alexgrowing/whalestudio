import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvalues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist

noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.SatInd

section Abstract

open GlobalTheory.LFun.SatCompare

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ G V} {K : Subgroup G}

theorem idem_mem_of_orbit (hs : IsSmooth π) (hi : π.IsIrreducible) (hc : IsCompact (K : Set G)) (S : Submodule ℂ V)
    {y : V} (h0 : y ≠ 0) (h : ∀ g, idem hs hc (π g y) ∈ S) (v : V) : idem hs hc v ∈ S := by
  obtain ⟨a, rfl⟩ := orbitMap_surjective hi h0 v
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    have : orbitMap π y (MonoidAlgebra.of ℂ G g) = π g y := by
      show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) y = _
      simp
    rw [this]; exact h g
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  | smul r a ha => rw [map_smul, map_smul]; exact S.smul_mem _ ha

theorem exists_scalar [TopologicalSpace.SeparableSpace G] (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (hcomm : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) :
    ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x := by
  intro h hh
  by_cases hb : fixed π K = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    have := heckeVec_mem_fixed hK hh hx
    rw [hb] at this
    simpa using this
  have : Nontrivial (fixed π K) := Submodule.nontrivial_iff_ne_bot.2 hb
  let A : Module.End ℂ (fixed π K) := (heckeLin hK hh π).restrict fun x hx => heckeVec_mem_fixed hK hh hx
  obtain ⟨c, hcA⟩ := exists_not_isUnit_sub
    ((Submodule.rank_le _).trans (rank_le_aleph0_of_isIrreducible hs hi)) A
  let B : V →ₗ[ℂ] V := heckeLin hK hh π - c • LinearMap.id
  have hB : ∀ x, B x = heckeVec π K h x - c • x := fun _ => rfl
  have hBf : ∀ x ∈ fixed π K, B x ∈ fixed π K := fun x hx =>
    sub_mem (heckeVec_mem_fixed hK hh hx) (Submodule.smul_mem _ _ hx)
  have key : ∀ g, ∀ x ∈ fixed π K, idem hs hc (π g (B x)) = B (idem hs hc (π g x)) := fun g x hx => by
    have hm := Final.DosetIndMem G K ℂ g
    refine smul_right_injective V (GlobalTheory.LGrp.Zonal.card_ne_zero hK g) ?_
    show _ • _ = _ • _
    rw [← map_smul B, ← GlobalTheory.LGrp.Zonal.heckeVec_dosetInd hs hc hK hx,
      ← GlobalTheory.LGrp.Zonal.heckeVec_dosetInd hs hc hK (hBf x hx), hB, hB, ← heckeVec_conv hK hh hm hx, hcomm _ hh _ hm,
      heckeVec_conv hK hm hh hx, ← heckeVec_smul hK hm]
    exact (heckeLin hK hm π).map_sub _ _
  refine ⟨c, fun x hx => ?_⟩
  by_cases hinj : ∃ y ∈ fixed π K, y ≠ 0 ∧ B y = 0
  · obtain ⟨y, hy, h0, e⟩ := hinj
    have := idem_mem_of_orbit hs hi hc (LinearMap.ker B) h0
      (fun g => by rw [LinearMap.mem_ker, ← key g y hy, e, map_zero, map_zero]) x
    rw [idem_of_mem hs hc hx] at this
    exact sub_eq_zero.1 this
  · push Not at hinj
    refine absurd ((Module.End.isUnit_iff _).2 ⟨(injective_iff_map_eq_zero _).2 fun y e => ?_, fun z => ?_⟩) hcA
    · by_contra h0
      exact hinj y y.2 (fun e' => h0 (Subtype.ext e')) (congrArg Subtype.val e)
    · obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 hb
      have := idem_mem_of_orbit hs hi hc ((fixed π K).map B) (hinj y hy h0)
        (fun g => by rw [key g y hy]; exact ⟨_, idem_mem hs hc _, rfl⟩) z
      rw [idem_of_mem hs hc z.2] at this
      obtain ⟨u, hu, e⟩ := this
      exact ⟨⟨u, hu⟩, Subtype.ext e⟩

theorem exists_idem_eq_smul (hs : IsSmooth π) (hi : π.IsIrreducible) (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) (hH : ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed π K, heckeVec π K h x = c • x)
    {x : V} (hx : x ∈ fixed π K) (h0 : x ≠ 0) (v : V) : ∃ c : ℂ, idem hs hc v = c • x := by
  have := idem_mem_of_orbit hs hi hc (Submodule.span ℂ {x}) h0 (fun g => by
    obtain ⟨c, e⟩ := hH _ (Final.DosetIndMem G K ℂ g)
    have e1 := e x hx
    rw [GlobalTheory.LGrp.Zonal.heckeVec_dosetInd hs hc hK hx] at e1
    rw [← inv_smul_smul₀ (GlobalTheory.LGrp.Zonal.card_ne_zero hK g) (idem hs hc (π g x)), e1, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) v
  obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 this
  exact ⟨c, e.symm⟩

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {U : ∀ a, Subgroup (Γ a)}

theorem map_idem_of_fixed (hs : ∀ a, IsSmooth (ρ a)) (hc : ∀ a, IsCompact (U a : Set (Γ a))) {v : ⨂[ℂ] a, X a}
    (hv : ∀ g : ∀ a, Γ a, (∀ a, g a ∈ U a) → piTensor ρ g v = v) :
    PiTensorProduct.map (fun a => idem (hs a) (hc a)) v = v := by
  classical
  have hC : IsCompact (Subgroup.pi Set.univ U : Set (∀ a, Γ a)) := isCompact_univ_pi hc
  have hS := isSmooth_piTensor hs
  have h1 : ∀ (x : ∀ a, X a) (i : α) (y : X i),
      idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i (idem (hs i) (hc i) y))) =
        idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i y)) := fun x i y => by
    let l : X i →ₗ[ℂ] ⨂[ℂ] a, X a := idem hS hC ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i
    have hk : twKer (ρ i) (U i) 1 ≤ LinearMap.ker l := Submodule.span_le.2 (by
      rintro _ ⟨u, z, rfl⟩
      show l _ = 0
      rw [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]
      have hu : Pi.mulSingle i (u : Γ i) ∈ Subgroup.pi Set.univ U := fun a _ => by
        show (Pi.mulSingle i (u : Γ i) : ∀ a, Γ a) a ∈ U a
        by_cases e : a = i
        · subst e; simp
        · rw [Pi.mulSingle_eq_of_ne e]; exact one_mem _
      refine Eq.trans ?_ (idem_apply_mem hS hC hu (PiTensorProduct.tprod ℂ (Function.update x i z)))
      rw [piTensor_tprod]
      show idem hS hC (PiTensorProduct.tprod ℂ _) = _
      congr 2
      funext a
      by_cases e : a = i
      · subst e; simp
      · simp [e])
    have h2 : l (idem (hs i) (hc i) y - y) = 0 := hk ((idem_eq_zero_iff (hs i) (hc i)).1 (by
      rw [map_sub, idem_of_mem _ _ (idem_mem _ _ _), sub_self]))
    rwa [map_sub, sub_eq_zero] at h2
  have h2 : ∀ (x : ∀ a, X a) (s : Finset α),
      idem hS hC (PiTensorProduct.tprod ℂ (s.piecewise (fun a => idem (hs a) (hc a) (x a)) x)) =
        idem hS hC (PiTensorProduct.tprod ℂ x) := fun x s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.piecewise_insert, h1, ← ih, ← Finset.piecewise_eq_of_notMem s (fun a => idem (hs a) (hc a) (x a)) x hi,
        Function.update_eq_self]
  have h3 : ∀ u, PiTensorProduct.map (fun a => idem (hs a) (hc a)) u = idem hS hC u := fun u => by
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, map_smul, PiTensorProduct.map_tprod, ← h2 x Finset.univ, Finset.piecewise_univ, idem_of_mem]
      refine GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_
      rw [piTensor_tprod]
      congr 1
      funext a
      exact GlobalTheory.LGrp.mem_fixed.1 (idem_mem _ _ _) _ (hg a trivial)
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h3, idem_of_mem hS hC (GlobalTheory.LGrp.mem_fixed.2 fun g hg => hv g fun a => hg a trivial)]

end Abstract

section Induction

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Levi k m) W}

theorem deltaHalf_eq_one {g : Levi k m} (hg : ∀ a, g a ∈ KO k (m a)) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  exact Finset.prod_eq_one fun a _ => Units.ext (by simp [val_absPow, LeviInt.nabs_det_eq_one (hg a)])

theorem apply_mul_of_fixed {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KO k n)) (g : GL n k) {x : GL n k}
    (hx : x ∈ KO k n) : f.1.1 (g * x) = f.1.1 g :=
  congrFun (congrArg (fun φ : IndSp e ρ => φ.1.1) (GlobalTheory.LGrp.mem_fixed.1 hf x hx)) g

theorem eq_zero_of_apply_one {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KO k n)) (h : f.1.1 1 = 0) : f = 0 := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  obtain ⟨p, hp, x, hx, rfl⟩ := (LeviInt.levi_integral_facts k α n m e).2.2.2.2.2.2.2.2 g
  have := parInd_law e ρ f ⟨p, hp⟩ 1
  rw [mul_one, h, map_zero, smul_zero] at this
  exact (apply_mul_of_fixed e hf p hx).trans this

theorem apply_one_fixed {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KO k n)) (g : Levi k m)
    (hg : ∀ a, g a ∈ KO k (m a)) : ρ g (f.1.1 1) = f.1.1 1 := by
  have h1 := parInd_law e ρ f ⟨_, leviEmb_mem_parab k e g⟩ 1
  have h2 := ((LeviInt.levi_integral_facts k α n m e).1 g 1 (one_mem _)).2 ⟨hg, one_mem _⟩
  rw [leviProj_leviEmb, deltaHalf_eq_one hg, Units.val_one, one_smul] at h1
  rw [← h1, ← apply_mul_of_fixed e hf 1 h2, one_mul]

theorem exists_fixed_apply_one {x : W} (hx : ∀ g : Levi k m, (∀ a, g a ∈ KO k (m a)) → ρ g x = x) :
    ∃ f ∈ fixed (parInd e ρ) (KO k n), f.1.1 1 = x := by
  obtain ⟨-, h1, -, -, -, -, -, -, h2⟩ := LeviInt.levi_integral_facts k α n m e
  choose p hp u hu hpu using h2
  let τ := (twist ρ (deltaHalf k m)).comp (leviProj k e)
  have h3 : ∀ q : parab k e, (q : GL n k) ∈ KO k n → τ q x = x := fun q hq => by
    show (deltaHalf k m (leviProj k e q) : ℂ) • ρ (leviProj k e q) x = x
    rw [deltaHalf_eq_one (h1 q hq), hx _ (h1 q hq), Units.val_one, one_smul]
  have h4 : ∀ (q : parab k e) y, y ∈ KO k n → τ ⟨p (q * y), hp _⟩ x = τ q x := fun q y hy => by
    have : (⟨p (q * y), hp _⟩ : parab k e) = q * (q⁻¹ * ⟨p (q * y), hp _⟩) := by group
    rw [this, map_mul, Module.End.mul_apply, h3]
    have e1 : ((q⁻¹ * ⟨p (q * y), hp _⟩ : parab k e) : GL n k) = y * (u (q * y))⁻¹ := by
      show (q : GL n k)⁻¹ * p (q * y) = _
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hpu, inv_mul_cancel_left]
    rw [e1]
    exact mul_mem hy (inv_mem (hu _))
  have h5 : ∀ y ∈ KO k n, ∀ g, τ ⟨p (g * y), hp _⟩ x = τ ⟨p g, hp _⟩ x := fun y hy g => by
    have := h4 ⟨p g, hp g⟩ (u g * y) (mul_mem (hu g) hy)
    simpa only [← mul_assoc, ← hpu] using this
  let φ : indSpace (parab k e) τ := ⟨fun g => τ ⟨p g, hp g⟩ x, fun q g => by
    have := h4 (q * ⟨p g, hp g⟩) (u g) (hu g)
    rw [map_mul, Module.End.mul_apply] at this
    simpa only [Subgroup.coe_mul, mul_assoc, ← hpu] using this⟩
  refine ⟨⟨φ, mem_smoothPart_of_nhds (Filter.mem_of_superset (GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (one_mem _))
    fun g hg => Subtype.ext (funext (h5 g hg)))⟩,
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => Subtype.ext (Subtype.ext (funext (h5 g hg))), ?_⟩
  have := h4 1 1 (one_mem _)
  simpa using this

variable {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  {π : ∀ a, Representation ℂ (GL (m a) k) (X a)}

theorem heckeVec_multiProd (hK : IsCommensurated (KO k n)) {h : GL n k → ℂ} (hh : h ∈ Hecke ℂ (KO k n))
    (hs : ∀ a, IsSmooth (π a)) {x : ∀ a, X a} {f : IndSp e (piTensor π)} (hf : f ∈ fixed (multiProd e π) (KO k n))
    {r : ℂ} (h1 : f.1.1 1 = r • PiTensorProduct.tprod ℂ x) (p : GL n k ⧸ KO k n → parab k e)
    (hp : ∀ c, ((p c : GL n k) : GL n k ⧸ KO k n) = c) (ω : GL n k ⧸ KO k n → α → ℂ)
    (hω : ∀ c, h (p c) ≠ 0 → ∀ a,
      idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (π a (leviProj k e (p c) a) (x a)) = ω c a • x a) :
    heckeVec (multiProd e π) (KO k n) h f =
      (∑ᶠ c, h (p c) * (deltaHalf k m (leviProj k e (p c)) : ℂ) * ∏ a, ω c a) • f := by
  have hf' := SatCompare.heckeVec_mem_fixed hK hh hf
  rw [← sub_eq_zero]
  refine eq_zero_of_apply_one e (sub_mem hf' (Submodule.smul_mem _ _ hf)) (sub_eq_zero.2 ?_)
  have hfin : (Function.support fun c => h (p c)).Finite :=
    (Formalism.UG.P.finite_support_cosets hK hh.2).subset fun c hc h0 => hc (by
      have hk : (c.out)⁻¹ * (p c : GL n k) ∈ KO k n := QuotientGroup.eq.1 (c.out_eq'.trans (hp c).symm)
      have := hh.1 1 ⟨_, hk⟩ c.out
      simp only [OneMemClass.coe_one, one_mul, mul_inv_cancel_left] at this
      exact this.trans h0)
  let L : IndSp e (piTensor π) →ₗ[ℂ] ⨂[ℂ] a, X a :=
    PiTensorProduct.map (fun a => idem (hs a) GlobalTheory.SplitFlip.isCompact_KO) ∘ₗ (LinearMap.proj (1 : GL n k)) ∘ₗ
      Submodule.subtype _ ∘ₗ Submodule.subtype _
  refine (map_idem_of_fixed hs (fun _ => GlobalTheory.SplitFlip.isCompact_KO) (apply_one_fixed e hf')).symm.trans ?_
  show L (heckeVec (multiProd e π) (KO k n) h f) = (_ : ℂ) • f.1.1 1
  rw [heckeVec_eq_of_section hh.1 hf _ hp, finsum_eq_sum_of_support_subset (s := hfin.toFinset),
    finsum_eq_sum_of_support_subset (s := hfin.toFinset), map_sum, Finset.sum_smul]
  · refine Finset.sum_congr rfl fun c hc => ?_
    rw [map_smul, mul_assoc, mul_smul]
    congr 1
    show PiTensorProduct.map _ (f.1.1 (1 * (p c : GL n k))) = _
    have := parInd_law e _ f (p c) 1
    rw [mul_one] at this
    rw [one_mul, this, h1, map_smul, map_smul, map_smul, piTensor_tprod, PiTensorProduct.map_tprod,
      funext (hω c (hfin.mem_toFinset.1 hc)), MultilinearMap.map_smul_univ, mul_smul, smul_comm r]
  · exact fun c hc => hfin.mem_toFinset.2 fun h0 => hc (by simp [show h (p c) = 0 from h0])
  · exact fun c hc => hfin.mem_toFinset.2 fun h0 => hc (by simp [show h (p c) = 0 from h0])

end Induction

section Completion

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isCompact_KGL : IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) := by
  rw [KGL, ← SphCompletion.KO_completion w n]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem exists_scalar_GL {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) :
    ∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ x ∈ fixed π (KGL w n), heckeVec π (KGL w n) h x = c • x :=
  haveI := secondCountableTopology_GL (w.adicCompletion E) (Fin n)
  exists_scalar hs hi isCompact_KGL (Final.GLintComm E w n) (Final.HeckeCommGL E w n ℂ)

theorem exists_hasSatGL_of_isIrreducible {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) (h : GlobalTheory.LGrp.IsSpherical π (KGL w n)) : ∃ B, HasSatGL w π B :=
  ExSatGL.exists_hasSatGL E w n V π h (exists_scalar_GL hs hi)

theorem dosetInd_eq_Tj {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {g : GL (Fin n) (w.adicCompletion E)}
    (h1 : IntM g) (h2 : IntM (tor h0 (fun _ => 1) * g⁻¹)) :
    ∃ j ≤ n, dosetInd ℂ (KGL w n) g = Tj ℂ n (Ov E w) ϖ j := by
  obtain ⟨a, ha, c, hc, d, hd, rfl⟩ := cartan h0 hu g
  have a0 : ∀ i, 0 ≤ a i := (intM_tor h0 hu a).1 (intM_doset h1 ⟨c⁻¹, inv_mem hc, d⁻¹, inv_mem hd, by group⟩)
  have a1 : ∀ i, 0 ≤ 1 - a i := (intM_tor h0 hu (fun _ => 1 - a _)).1 (intM_doset h2 ⟨d, hd, c, hc, by
    have e : tor h0 (fun i => 1 - a i) * tor h0 a = tor h0 fun _ => 1 := by
      rw [← tor_add]; congr 1; funext i; simp
    rw [← mul_assoc, ← tor_const_comm, ← e]; group⟩)
  set j := (Finset.univ.filter fun i => 0 < a i).card
  have hj : ∀ i : Fin n, 0 < a i ↔ (i : ℕ) < j := fun i =>
    (Fin.lt_card_filter_univ_iff_apply_of_imp (fun i => 0 < a i) fun x y hxy hx => lt_of_lt_of_le hx (ha hxy)).symm
  refine ⟨j, by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun i => 0 < a i, ?_⟩
  rw [dosetInd_congr ⟨c, hc, d, hd, rfl⟩, Tj_eq h0]
  congr 2
  funext i
  have := hj i
  have := a0 i
  have := a1 i
  split_ifs <;> omega

theorem intM_of_Tj {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {g : GL (Fin n) (w.adicCompletion E)}
    {j : ℕ} (h : Tj ℂ n (Ov E w) ϖ j g ≠ 0) : IntM g ∧ IntM (tor h0 (fun _ => 1) * g⁻¹) := by
  rw [Tj_eq h0] at h
  obtain ⟨c, hc, d, hd, rfl⟩ := mem_doset.1 (Set.mem_of_indicator_ne_zero h)
  refine ⟨intM_doset ((intM_tor h0 hu _).2 fun i => by split_ifs <;> simp) ⟨c, hc, d, hd, rfl⟩,
    intM_doset ((intM_tor h0 hu fun i => if (i : ℕ) < j then 0 else 1).2 fun i => by split_ifs <;> simp)
      ⟨d⁻¹, inv_mem hd, c⁻¹, inv_mem hc, ?_⟩⟩
  have e : (tor h0 fun i : Fin n => if (i : ℕ) < j then 0 else 1) * (tor h0 fun i => if (i : ℕ) < j then 1 else 0) =
      tor h0 fun _ => 1 := by
    rw [← tor_add]; congr 1; funext i; simp only [Pi.add_apply]; split_ifs <;> simp
  rw [mul_inv_rev, mul_inv_rev, ← mul_assoc, tor_const_comm, ← e]; group

theorem idem_of_isSatVecGL {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} (hs : IsSmooth π) {x : V}
    {B : Multiset ℂˣ} (hx : IsSatVecGL w π x B) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : dosetInd ℂ (KGL w n) g = Tj ℂ n (Ov E w) ϖ j) :
    idem hs (H := KO _ (Fin n)) GlobalTheory.SplitFlip.isCompact_KO (π g x) =
      ((((P.finite_cosets_in_doset (Final.GLintComm E w n) g).toFinset.card : ℂ))⁻¹ * satEig (qV E w) n B j) • x := by
  have h := GlobalTheory.LGrp.Zonal.heckeVec_dosetInd hs isCompact_KGL (Final.GLintComm E w n) hx.2.1 g
  rw [hg, hx.2.2.2 ϖ hu j hj] at h
  rw [mul_smul, h, inv_smul_smul₀ (GlobalTheory.LGrp.Zonal.card_ne_zero (Final.GLintComm E w n) g)]
  congr 2
  exact SphCompletion.KO_completion w n

theorem val_absPow_completion (s : ℂ) (x : (w.adicCompletion E)ˣ) :
    (absPow (w.adicCompletion E) s x : ℂ) = (qV E w : ℂ) ^ (-(ordV E w x : ℂ) * s) := by
  rw [val_absPow, GlobalTheory.LGrp.BorelCompletion.nabs_completion, GlobalTheory.LGrp.BorelCompletion.ordV_eq, ← Real.rpow_intCast,
    ← Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg _)]
  push_cast
  rw [neg_neg]

variable {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)

theorem val_stdBlocks (a : Fin c) (i : Fin (N a)) : (stdBlocks N h ⟨a, i⟩ : ℕ) = ∑ b with b < a, N b + i := by
  rw [stdBlocks_val]
  congr 1
  exact Finset.sum_bij (fun b _ => Fin.castLE a.2.le b) (fun b _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, b.2⟩)
    (fun _ _ _ _ e => Fin.castLE_injective _ e) (fun b hb => ⟨⟨b, (Finset.mem_filter.1 hb).2⟩, Finset.mem_univ _, rfl⟩)
    fun _ _ => rfl

theorem mem_parab_of_isUpperB {b : GL (Fin n) (w.adicCompletion E)} (hb : IsUpperB E w b) :
    b ∈ parab (w.adicCompletion E) (stdBlocks N h) := by
  refine mem_parab_iff.2 fun x y i j hxy => hb _ _ ?_
  rw [Fin.lt_def, val_stdBlocks, val_stdBlocks]
  have h1 : ∑ b ∈ insert y (Finset.univ.filter (· < y)), N b ≤ ∑ b with b < x, N b :=
    Finset.sum_le_sum_of_subset fun b hb => by
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hb.elim (fun e => e ▸ hxy) fun e => e.trans hxy
  rw [Finset.sum_insert (by simp)] at h1
  have := j.2
  omega

theorem isUpperB_leviProj {b : parab (w.adicCompletion E) (stdBlocks N h)} (hb : IsUpperB E w b.1) (a : Fin c) :
    IsUpperB E w (leviProj _ _ b a) := fun i j hij => hb _ _ (by
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val]; exact Nat.add_lt_add_left hij _)

theorem chiDelta_eq {β : ∀ a, Fin (N a) → ℂ} {γ : Fin n → ℂ} (hγ : ∀ a i, γ (stdBlocks N h ⟨a, i⟩) = β a i)
    {b : parab (w.adicCompletion E) (stdBlocks N h)} (hb : IsUpperB E w b.1) :
    chiDelta E w γ b.1 = (deltaHalf _ _ (leviProj _ _ b) : ℂ) * ∏ a, chiDelta E w (β a) (leviProj _ _ b a) := by
  rw [chiDelta, ← (stdBlocks N h).prod_comp, Fintype.prod_sigma, deltaHalf_apply, Units.coe_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hd : (leviProj _ _ b a).val.det = ∏ i, (leviProj _ _ b a).val i i :=
    Matrix.det_of_isUpperTriangular fun i j hij => isUpperB_leviProj h hb a i j hij
  have h0 : ∀ i, (leviProj _ _ b a).val i i ≠ 0 := fun i e =>
    (Matrix.GeneralLinearGroup.det (leviProj _ _ b a)).ne_zero (hd.trans (Finset.prod_eq_zero (Finset.mem_univ i) e))
  have hd' : Matrix.GeneralLinearGroup.det (leviProj _ _ b a) = ∏ i, Units.mk0 _ (h0 i) :=
    Units.ext (by rw [Units.coe_prod]; exact hd)
  rw [hd', map_prod, Units.coe_prod, chiDelta, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hq : (qV E w : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (qV_ne_zero w)
  rw [val_absPow_completion, hγ, mul_left_comm, ← Complex.cpow_add _ _ hq, val_stdBlocks]
  have hn : n = ∑ b with b < a, N b + N a + ∑ b with a < b, N b := by
    have : ∀ b, N b = (if b < a then N b else 0) + (if b = a then N b else 0) + if a < b then N b else 0 := fun b => by
      rcases lt_trichotomy b a with e | e | e
      · simp [e, e.ne, e.not_gt]
      · simp [e]
      · simp [e, e.ne', e.not_gt]
    rw [← h, Finset.sum_congr rfl fun b _ => this b, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_filter, Finset.sum_filter]
    simp
  have hn' := congrArg (Nat.cast : ℕ → ℂ) hn
  simp only [modExp, Fintype.card_fin, Units.val_mk0, leviProj_apply]
  push_cast at hn' ⊢
  rw [hn']
  congr 2
  ring

omit h in

theorem exists_model {S : Multiset ℂˣ} (hS : S.card = n) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (R : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X)
      (β : Fin n → ℂˣ) (l : X →ₗ[ℂ] ℂ) (y : X), IsSmooth R ∧ Finset.univ.val.map β = S ∧ IsSatVecGL w R y S ∧ l y = 1 ∧
        ∀ g, IsUpperB E w g → ∀ z, l (R g z) = chiDelta E w (fun i => (β i : ℂ)) g * l z := by
  obtain ⟨β, rfl⟩ : ∃ β : Fin n → ℂˣ, Finset.univ.val.map β = S := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep S
    obtain rfl : l.length = n := hS
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨φ, hφ, hφ1, -⟩ := Final.SphericalExists E w n (fun i => (β i : ℂ)) fun i => (β i).ne_zero
  obtain ⟨y, -, rfl⟩ := (SphCompletion.isSpherical_iff E w n β φ).1 hφ
  refine ⟨_, _, _, prinSeries fun i => unrChar (w.adicCompletion E) (β i), β,
    LinearMap.proj 1 ∘ₗ Submodule.subtype _ ∘ₗ Submodule.subtype _, y, isSmooth_parInd _ _, rfl, ?_, hφ1,
    fun g hg z => ?_⟩
  · exact IsSatVecGL.of_map (ρ' := rightReg ℂ _ ℂ) ((Submodule.subtype _).comp (Submodule.subtype _))
      (fun _ _ => rfl) (fun u v e => Subtype.ext (Subtype.ext e))
      (isSatVecGL_of_isSpherical hφ fun e => one_ne_zero (hφ1.symm.trans (congrFun e 1)))
  · have := (parInd_law _ _ z ⟨g, (mem_borel _).2 hg⟩ 1).trans
      (SphCompletion.law_completion w n β ⟨g, (mem_borel _).2 hg⟩ _)
    rw [mul_one] at this
    exact (congrArg z.1.1 (one_mul _)).trans this

theorem exists_map_isSatVecGL {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {R : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a)} {β : ∀ a, Fin (N a) → ℂˣ}
    {l : ∀ a, X a →ₗ[ℂ] ℂ} {y : ∀ a, X a} (h1 : ∀ a, l a (y a) = 1)
    (hl : ∀ a g, IsUpperB E w g → ∀ z, l a (R a g z) = chiDelta E w (fun i => (β a i : ℂ)) g * l a z)
    {F : IndSp (stdBlocks N h) (piTensor R)} (hF : F ∈ fixed (multiProd (stdBlocks N h) R) (KO _ (Fin n)))
    (hF1 : F.1.1 1 = PiTensorProduct.tprod ℂ y) :
    ∃ Y : IndSp (stdBlocks N h) (piTensor R) →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ),
      (∀ g z, Y (multiProd (stdBlocks N h) R g z) = rightReg ℂ _ ℂ g (Y z)) ∧
        IsSatVecGL w (rightReg ℂ _ ℂ) (Y F) (∑ a, Finset.univ.val.map (β a)) := by
  obtain ⟨ev, hev⟩ : ∃ ev : (⨂[ℂ] a, X a) →ₗ[ℂ] ℂ, ∀ u, ev (PiTensorProduct.tprod ℂ u) = ∏ a, l a (u a) :=
    ⟨PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin c) ℂ).compLinearMap l), fun u => by simp⟩
  have hlaw : ∀ g : ∀ a, GL (Fin (N a)) (w.adicCompletion E), (∀ a, IsUpperB E w (g a)) → ∀ u,
      ev (piTensor R g u) = (∏ a, chiDelta E w (fun i => (β a i : ℂ)) (g a)) * ev u := fun g hg u => by
    induction u using PiTensorProduct.induction_on with
    | smul_tprod t z =>
      rw [map_smul, map_smul, map_smul, piTensor_tprod, hev, hev, smul_eq_mul, smul_eq_mul, mul_left_comm,
        ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun a _ => hl a _ (hg a) _]
    | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', mul_add]
  let γ : Fin n → ℂˣ := (fun s : Σ a, Fin (N a) => β s.1 s.2) ∘ (stdBlocks N h).symm
  have hγ : Finset.univ.val.map γ = ∑ a, Finset.univ.val.map (β a) := by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv, ← Finset.univ_sigma_univ]
    simp only [Finset.sigma, Multiset.sigma, Multiset.map_bind, Multiset.map_map]
    rfl
  let Y : IndSp (stdBlocks N h) (piTensor R) →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ) :=
    ev.compLeft _ ∘ₗ Submodule.subtype _ ∘ₗ Submodule.subtype _
  have hY1 : Y F 1 = 1 := by
    show ev (F.1.1 1) = 1
    rw [hF1, hev]
    exact Finset.prod_eq_one fun a _ => h1 a
  refine ⟨Y, fun _ _ => rfl, ?_⟩
  rw [← hγ]
  refine isSatVecGL_of_isSpherical (fun b g u hb hu => ?_) fun e => one_ne_zero (hY1.symm.trans (congrFun e 1))
  show ev (F.1.1 (b * g * u)) = _ * ev (F.1.1 g)
  rw [← SphCompletion.KO_completion w n] at hu
  rw [apply_mul_of_fixed _ hF _ hu, parInd_law _ _ F ⟨b, mem_parab_of_isUpperB h hb⟩ g, map_smul,
    hlaw _ (isUpperB_leviProj h hb), smul_eq_mul, ← mul_assoc,
    ← chiDelta_eq h (β := fun a i => (β a i : ℂ)) (γ := fun i => (γ i : ℂ)) (b := ⟨b, mem_parab_of_isUpperB h hb⟩)
      (fun a i => congrArg (fun s : Σ a, Fin (N a) => (β s.1 s.2 : ℂ)) ((stdBlocks N h).symm_apply_apply ⟨a, i⟩)) hb]

theorem exists_sat_multiProd {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {π : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a)} (hs : ∀ a, IsSmooth (π a))
    (hi : ∀ a, (π a).IsIrreducible) {f : IndSp (stdBlocks N h) (piTensor π)}
    (hf : f ∈ fixed (multiProd (stdBlocks N h) π) (KGL w n)) (h0 : f ≠ 0) :
    ∃ S : Fin c → Multiset ℂˣ, (∀ a, HasSatGL w (π a) (S a)) ∧
      IsSatVecGL w (multiProd (stdBlocks N h) π) f (∑ a, S a) := by
  have hKO : ∀ m, KGL w m = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hf' := hf
  rw [hKO] at hf'
  have hv := map_idem_of_fixed hs (fun _ => GlobalTheory.SplitFlip.isCompact_KO) (apply_one_fixed _ hf')
  have hsph : ∀ a, GlobalTheory.LGrp.IsSpherical (π a) (KGL w (N a)) := fun a e => by
    rw [hKO] at e
    refine h0 (eq_zero_of_apply_one _ hf' (hv.symm.trans ?_))
    generalize f.1.1 1 = u
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, PiTensorProduct.map_tprod, MultilinearMap.map_coord_zero _ a, smul_zero]
      have := idem_mem (hs a) GlobalTheory.SplitFlip.isCompact_KO (x a)
      rwa [e] at this
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  choose S hS using fun a => exists_hasSatGL_of_isIrreducible (hs a) (hi a) (hsph a)
  choose x hx using fun a => (hS a).exists_vec
  have hr : ∀ u, ∃ r : ℂ, PiTensorProduct.map (fun a => idem (hs a) (H := KO _ _) GlobalTheory.SplitFlip.isCompact_KO) u =
      r • PiTensorProduct.tprod ℂ x := fun u => by
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r y =>
      choose t ht using fun a => exists_idem_eq_smul (hs a) (hi a) GlobalTheory.SplitFlip.isCompact_KO
        (hKO _ ▸ Final.GLintComm E w (N a)) (hKO _ ▸ exists_scalar_GL (hs a) (hi a)) (hKO _ ▸ (hx a).2.1) (hx a).1 (y a)
      exact ⟨r * ∏ a, t a, by
        rw [map_smul, PiTensorProduct.map_tprod, funext ht, MultilinearMap.map_smul_univ, mul_smul]⟩
    | add y z hy hz =>
      obtain ⟨r, hr⟩ := hy
      obtain ⟨t, ht⟩ := hz
      exact ⟨r + t, by rw [map_add, hr, ht, add_smul]⟩
  obtain ⟨r, hr⟩ := hr (f.1.1 1)
  rw [hv] at hr
  choose Z iZ mZ R β l y hR hβ hyS h1 hl using fun a => exists_model (w := w) (hS a).card
  have hy : ∀ a, y a ∈ fixed (R a) (KO _ _) := fun a => hKO _ ▸ (hyS a).2.1
  obtain ⟨F, hF, hF1⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor R) (x := PiTensorProduct.tprod ℂ y)
    fun g hg => by
      rw [piTensor_tprod]
      congr 1
      exact funext fun a => GlobalTheory.LGrp.mem_fixed.1 (hy a) _ (hg a)
  obtain ⟨Y, hYe, hY⟩ := exists_map_isSatVecGL h h1 hl hF hF1
  rw [funext hβ] at hY
  refine ⟨S, hS, h0, hf, hY.2.2.1, fun ϖ hϖ j hj => ?_⟩
  have hϖ0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ
  have hT := Tj_mem_hecke (n := n) hϖ j
  have hK : IsCommensurated (KGL w n) := Final.GLintComm E w n
  have e1 := (map_heckeVec (ρ := multiProd (stdBlocks N h) R) hK hT Y hYe F).trans (hY.2.2.2 ϖ hϖ j hj)
  rw [hKO] at hT hK e1 ⊢
  have hp : ∀ q : GL (Fin n) (w.adicCompletion E) ⧸ KO (w.adicCompletion E) (Fin n),
      ∃ p : parab (w.adicCompletion E) (stdBlocks N h), ((p : GL (Fin n) (w.adicCompletion E)) : _ ⧸ KO _ _) = q :=
    fun q => by
      obtain ⟨p, hp, u, hu, e⟩ := (LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).2.2.2.2.2.2.2.2 q.out
      exact ⟨⟨p, hp⟩, (QuotientGroup.eq.2 (by simpa [e] using hu)).trans q.out_eq'⟩
  choose p hp using hp
  have hω : ∀ q a, ∃ t : ℂ, Tj ℂ n (Ov E w) ϖ j (p q) ≠ 0 →
      idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (π a (leviProj _ _ (p q) a) (x a)) = t • x a ∧
      idem (hR a) GlobalTheory.SplitFlip.isCompact_KO (R a (leviProj _ _ (p q) a) (y a)) = t • y a := fun q a => by
    by_cases hq : Tj ℂ n (Ov E w) ϖ j (p q) = 0
    · exact ⟨0, fun e => absurd hq e⟩
    obtain ⟨i1, i2⟩ := intM_of_Tj hϖ0 hϖ hq
    obtain ⟨l, hl, e⟩ := dosetInd_eq_Tj hϖ0 hϖ (g := leviProj _ _ (p q) a) (fun s t => i1 _ _) fun s t => by
      have := i2 (stdBlocks N h ⟨a, s⟩) (stdBlocks N h ⟨a, t⟩)
      rw [← Pi.inv_apply, ← map_inv]
      rw [Units.val_mul, tor_val, Matrix.diagonal_mul] at this ⊢
      exact this
    exact ⟨_, fun _ => ⟨idem_of_isSatVecGL (hs a) (hx a) hϖ hl e, idem_of_isSatVecGL (hR a) (hyS a) hϖ hl e⟩⟩
  choose ω hω using hω
  rw [heckeVec_multiProd _ hK hT hR hF (hF1.trans (one_smul ℂ _).symm) p hp ω (fun q hq a => (hω q a hq).2),
    map_smul] at e1
  rw [heckeVec_multiProd _ hK hT hs hf' hr p hp ω (fun q hq a => (hω q a hq).1), smul_left_injective ℂ hY.1 e1]

section Twist

variable {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
  {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W} {s : ℂ}

theorem absPow_det_of_mem (s : ℂ) {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ KGL w n) :
    absPow (w.adicCompletion E) s (Matrix.GeneralLinearGroup.det g) = 1 :=
  Units.ext (by
    rw [KGL, ← SphCompletion.KO_completion w n] at hg
    simp [val_absPow, LeviInt.nabs_det_eq_one hg])

theorem mem_fixed_twist (T : (twist ρ (detChar (Fin n) (absPow _ s))).Equiv ρ') (x : V) :
    T x ∈ fixed ρ' (KGL w n) ↔ x ∈ fixed ρ (KGL w n) := by
  simp only [GlobalTheory.LGrp.mem_fixed]
  refine forall₂_congr fun g hg => ?_
  have := T.toIntertwiningMap.isIntertwining _ _ g x
  rw [twist_apply, detChar_apply, absPow_det_of_mem s hg, Units.val_one, one_smul] at this
  exact (Eq.congr_left this.symm).trans T.toLinearEquiv.injective.eq_iff

theorem hasSatGL_of_twist (T : (twist ρ (detChar (Fin n) (absPow _ s))).Equiv ρ') {B : Multiset ℂˣ}
    (hB : HasSatGL w ρ B) {z : ℂˣ} (hz : (z : ℂ) = (qV E w : ℂ) ^ (-s)) : HasSatGL w ρ' (B.map (· * z)) := by
  constructor
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    exact (Submodule.ne_bot_iff _).2 ⟨T x, (mem_fixed_twist T x).2 hx,
      (map_ne_zero_iff T.toLinearEquiv T.toLinearEquiv.injective).2 h0⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.toLinearEquiv.surjective y
    have hx := hB.2 x ((mem_fixed_twist T x).1 hy) ((map_ne_zero_iff _ T.toLinearEquiv.injective).1 h0)
    refine ⟨h0, hy, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
    rw [GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← map_smul T.toLinearEquiv, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
    have e := T.toLinearEquiv.toAddEquiv.map_finsum
      (fun c : _ ⧸ KGL w n => Tj ℂ n (Ov E w) ϖ j c.out • ρ c.out x)
    rw [show T.toLinearEquiv _ = _ from e, smul_finsum]
    refine finsum_congr fun c => ?_
    by_cases hc : Tj ℂ n (Ov E w) ϖ j c.out = 0
    · simp [hc]
    obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hc
    have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
    have e2 : Matrix.GeneralLinearGroup.det c.out =
        Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ hϖ0 ^ j * Matrix.GeneralLinearGroup.det b := by
      apply Units.ext
      change c.out.val.det = a.val.det * _ * b.val.det
      rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ hj]
      simp
    have e3 : absPow (w.adicCompletion E) s (Units.mk0 ϖ hϖ0) = z := Units.ext (by
      have : ordV E w ϖ = 1 := by
        rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v ϖ = _ from hϖ]; rfl
      rw [val_absPow_completion, hz, Units.val_mk0, this]
      simp)
    have := T.toIntertwiningMap.isIntertwining _ _ c.out x
    rw [twist_apply, detChar_apply, e2, map_mul, map_mul, absPow_det_of_mem s ha, absPow_det_of_mem s hb, map_pow, e3,
      one_mul, mul_one, map_smul] at this
    refine (congrArg (Tj ℂ n (Ov E w) ϖ j c.out • ·) this.symm).trans ?_
    rw [smul_comm, Units.val_pow_eq_pow_val]
    congr 1
    exact (map_smul T.toLinearEquiv _ _).symm

end Twist

theorem exists_sat_of_isSpeh {a d : ℕ} (hd : 1 ≤ d) {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V}
    (hs : IsSmooth ρ) (hi : ρ.IsIrreducible) {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hσ : IsSpeh (IrrGL.of ρ hs hi) d σ) {B : Multiset ℂˣ} (hB : HasSatGL w σ B) :
    ∃ S, HasSatGL w ρ S ∧ ∑ k : Fin d, S.map (fun z : ℂˣ => (z : ℂ) * (qV E w : ℂ) ^ (((d : ℂ) - 1) / 2 - (k : ℕ))) =
      B.map (fun z : ℂˣ => (z : ℂ)) := by
  obtain ⟨hn, -, p, hp, -⟩ := hσ
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hx' := hx.2.1
  rw [← map_fixed_of_surjective (isSmooth_prodIrr _ hn) isCompact_KGL hp] at hx'
  obtain ⟨f, hf, rfl⟩ := hx'
  obtain ⟨R, hR, hfR⟩ := exists_sat_multiProd hn (fun k => (spehFactor (IrrGL.of ρ hs hi) d k).2.rep.smooth)
    (fun k => (spehFactor (IrrGL.of ρ hs hi) d k).2.rep.irr) hf fun e => hx.1 (by rw [e, map_zero])
  obtain rfl := hx.unique (hfR.map p.toLinearMap (fun g y => p.isIntertwining _ _ g y) hx.1)
  let T : ∀ k : Fin d, (twist ρ (detChar (Fin a) (absPow _ (((d : ℂ) - 1) / 2 - (k : ℕ))))).Equiv
      (spehFactor (IrrGL.of ρ hs hi) d k).rep := fun k =>
    (twistEquiv (IrrGL.equivOf ρ hs hi) _).trans ((IrrGL.of ρ hs hi).twEquiv _ (isSmoothChar_absPow _))
  obtain ⟨S, hS⟩ := exists_hasSatGL_of_isIrreducible hs hi (by
    obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 (hR ⟨0, hd⟩).1
    obtain ⟨y, rfl⟩ := (T ⟨0, hd⟩).toLinearEquiv.surjective y
    exact (Submodule.ne_bot_iff _).2 ⟨y, (mem_fixed_twist (T ⟨0, hd⟩) y).1 hy, fun e => h0 (by rw [e, map_zero])⟩)
  have hq : ∀ t : ℂ, (qV E w : ℂ) ^ t ≠ 0 := fun t h0 =>
    qV_ne_zero w (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h0).1)
  refine ⟨S, hS, ?_⟩
  refine Eq.trans ?_ (map_sum (Multiset.mapAddMonoidHom _) _ _).symm
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hR k).unique (hasSatGL_of_twist (T k) hS (z := Units.mk0 _ (hq _)) rfl), Multiset.coe_mapAddMonoidHom, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  have hk : ((k.rev : ℕ) : ℂ) = d - (k + 1) := by
    rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_of_lt k.2)]
    push_cast
    rfl
  simp only [Function.comp_apply, Units.val_mul, Units.val_mk0, Fin.revPerm_apply, hk]
  congr 2
  ring

end Completion

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefiniteBC GlobalTheory.BcSpeh

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem satake_locProd_speh : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c n : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (ρ : ∀ i, LocIrr w (a i)) (σ : ∀ i, LocIrr w (d i * a i)), (∀ i, 1 ≤ d i) → (∀ i, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i).ρ (ρ i).smooth (ρ i).irred) (d i) (σ i).ρ) → ∀ T : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w (locProd h w σ) T → ∃ S : Fin c → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) ∧ ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) = T.map (fun z => (z : ℂ)) := by
  intro E _ _ w c n a d h ρ σ hd hσ T hT
  obtain ⟨f, hf⟩ := hT.exists_vec
  obtain ⟨B, hB, hfB⟩ := exists_sat_multiProd h (fun i => (σ i).smooth) (fun i => (σ i).irred) hf.2.1 hf.1
  obtain rfl := hf.unique hfB
  choose S hS hS' using fun i => exists_sat_of_isSpeh (hd i) (ρ i).smooth (ρ i).irred (hσ i) (hB i)
  refine ⟨S, hS, ?_⟩
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  exact (Finset.sum_congr rfl fun i _ => hS' i).trans (map_sum (Multiset.mapAddMonoidHom _) _ _).symm

end GlobalTheory.SatInd

end
