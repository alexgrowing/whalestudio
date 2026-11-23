import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.OpenLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.SphericalSpanAlt

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private noncomputable def intPts (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Subgroup (finU L n) :=
  (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL L n).comap (GlobalTheory.BCT.GlobLev.finPart L n)

private theorem isOpen_intPts : IsOpen (intPts L n : Set (finU L n)) :=
  (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL L n).preimage GlobalTheory.BCT.GlobLev.continuous_finPart

private theorem isCompact_intPts : IsCompact (intPts L n : Set (finU L n)) := by
  refine IsCompact.of_isClosed_subset (GlobalTheory.BCT.GlobLev.isClosedEmbedding_finU.isCompact_preimage
    ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL L n).image GlobalTheory.BCT.GlobLev.continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ isOpen_intPts) fun x hx => ⟨GlobalTheory.BCT.GlobLev.finPart L n x, hx, ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf L) ((x : UA L n) : GA L n) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

private theorem mem_intPts {k : finU L n} (h : ∀ u, cLoc u (k : UA L n) ∈ GlobalTheory.LFun.KGL u n) : k ∈ intPts L n := by
  rw [intPts, Subgroup.mem_comap, GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles] at h ⊢
  exact ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩

end UpperTheory.V.Z.Sym.Al.SphericalSpanAlt

namespace UpperTheory.V.Z.Sym.Al.SphericalSpanAlt

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem finite_quot (w : Plc L) (U : Subgroup (UA L n))
    (hU : IsOpen {x : finU L n | (x : UA L n) ∈ U}) :
    Finite ((locU n w ⊓ Kall L n : Subgroup (UA L n)) ⧸ U.subgroupOf (locU n w ⊓ Kall L n)) := by
  haveI : CompactSpace (intPts L n) := isCompact_iff_compactSpace.1 isCompact_intPts
  let U' : Subgroup (finU L n) := U.subgroupOf (finU L n)
  have hU' : IsOpen (U' : Set (finU L n)) := hU
  let H : Subgroup (intPts L n) := U'.subgroupOf (intPts L n)
  have hH : IsOpen (H : Set (intPts L n)) := hU'.preimage continuous_subtype_val
  haveI : Finite (intPts L n ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hfin : ∀ k : (locU n w ⊓ Kall L n : Subgroup (UA L n)), (k : UA L n) ∈ finU L n := fun k =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 k.2).2).1
  have hint : ∀ (k : (locU n w ⊓ Kall L n : Subgroup (UA L n))) (u : Plc L),
      cLoc u (k : UA L n) ∈ GlobalTheory.LFun.KGL u n := fun k u =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 k.2).2).2 u)
  let f : (locU n w ⊓ Kall L n : Subgroup (UA L n)) →* intPts L n :=
    { toFun := fun k => ⟨⟨k.1, hfin k⟩, mem_intPts (hint k)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have e : U.subgroupOf (locU n w ⊓ Kall L n) = H.comap f := by
    ext k
    rfl
  rw [e]
  refine Finite.of_injective (fun q : _ ⧸ H.comap f => ((f (Quotient.out q) : intPts L n) : intPts L n ⧸ H))
    fun q q' e' => ?_
  have e'' := QuotientGroup.eq.1 e'
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  refine QuotientGroup.eq.2 ?_
  show f (_ * _) ∈ H
  rw [map_mul, map_inv]
  exact e''

private theorem sum_translate {G X : Type} [Group G] [AddCommMonoid X] (K : Subgroup G) (K' : Subgroup K)
    [Fintype (K ⧸ K')] (F : G → X) (hF : ∀ t, ∀ m ∈ K', F (t * ((m : K) : G)) = F t) (k : G) (hk : k ∈ K) (t : G) :
    ∑ q : K ⧸ K', F (t * k * ((Quotient.out q : K) : G)) = ∑ q : K ⧸ K', F (t * ((Quotient.out q : K) : G)) := by
  let kk : K := ⟨k, hk⟩
  have step : ∀ q : K ⧸ K', F (t * k * ((Quotient.out q : K) : G)) =
      F (t * ((Quotient.out (kk • q) : K) : G)) := by
    intro q
    have hm : (Quotient.out (kk • q))⁻¹ * (kk * Quotient.out q) ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [← hF (t * ((Quotient.out (kk • q) : K) : G)) _ hm]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, kk, mul_assoc, mul_inv_cancel_left]
  rw [Finset.sum_congr rfl fun q _ => step q]
  exact Fintype.sum_equiv (MulAction.toPerm kk) _ _ fun q => rfl

end UpperTheory.V.Z.Sym.Al.SphericalSpanAlt

open UpperTheory.V.Z.Sym.Al.SphericalSpanAlt in
theorem UpperTheory.V.Z.Sym.Al.spanSph :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w : Plc L, IsUnramU π w →
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → ∃ φ', φ' ≠ 0 ∧ InSpan w φ φ' ∧ ∀ x ∈ locU n w ⊓ Kall L n, ∀ g, φ' (g * x) = φ' g := by
  classical
  intro L _ _ _ n V _ _ _ π hπ w hw φ h0 hc
  obtain ⟨f1, f2, -, -, f5, -⟩ := factor L n w
  obtain ⟨ψ, hψ, hψ0, hψK⟩ := hw
  obtain ⟨g0, hg0⟩ := Function.ne_iff.1 h0
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f (φ g0) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
  have hhπ : f ∘ φ ∈ π := hc f
  have hh0 : f ∘ φ ≠ 0 := fun e => hf (congrFun e g0)
  have rmul : ∀ (a b : UA L n) (F : UA L n → ℂ), RU L n (a * b) F = RU L n a (RU L n b F) :=
    fun a b F => by rw [map_mul]; rfl

  let S := Submodule.span ℂ (Set.range fun g : UA L n => RU L n g (f ∘ φ))
  have hSπ : S ≤ π := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hπ.stable g _ hhπ)
  have hSst : ∀ a, ∀ F ∈ S, RU L n a F ∈ S := by
    intro a F hF
    have hle : S ≤ S.comap (RU L n a) := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      show RU L n a (RU L n g (f ∘ φ)) ∈ S
      rw [← rmul]
      exact Submodule.subset_span ⟨_, rfl⟩)
    exact hle hF
  have hhS : f ∘ φ ∈ S := by
    have h1 : RU L n 1 (f ∘ φ) = f ∘ φ := by rw [map_one]; rfl
    rw [← h1]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hSeq : S = π := by
    rcases hπ.irred S hSπ hSst with e | e
    · exact absurd ((Submodule.mem_bot ℂ).1 (e ▸ hhS)) hh0
    · exact e
  obtain ⟨c, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hSeq ▸ hψ : ψ ∈ S)

  choose x hx y hy hxy using f2
  let φg : UA L n → UA L n → V := fun g t => φ (t * x g)
  have hcoef : ∀ g, CoefIn (φg g) π := fun g f' => hπ.stable (x g) _ (hc f')
  choose U hUo hUf using fun g => openLev L n V π hπ (φg g) (hcoef g)
  let U0 : Subgroup (UA L n) := ⨅ g ∈ c.support, U g
  have hU0 : IsOpen {k : finU L n | (k : UA L n) ∈ U0} := by
    have e : {k : finU L n | (k : UA L n) ∈ U0} = ⋂ g ∈ c.support, {k : finU L n | (k : UA L n) ∈ U g} := by
      ext k
      simp only [U0, Subgroup.mem_iInf, Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact isOpen_biInter_finset fun g _ => hUo g
  let K : Subgroup (UA L n) := locU n w ⊓ Kall L n
  let K' : Subgroup K := U0.subgroupOf K
  haveI : Finite (K ⧸ K') := finite_quot w U0 hU0
  letI : Fintype (K ⧸ K') := Fintype.ofFinite _
  let rep : K ⧸ K' → UA L n := fun q => ((Quotient.out q : K) : UA L n)
  have hrepK : ∀ q, rep q ∈ K := fun q => (Quotient.out q).2
  have hrepl : ∀ q, rep q ∈ locU n w := fun q => (Subgroup.mem_inf.1 (hrepK q)).1
  let A : UA L n → UA L n → V := fun g t => ∑ q, φg g (t * rep q)
  have hψfix : ∀ k ∈ K, ∀ t, ψ (t * k) = ψ t := fun k hk t => by
    obtain ⟨k1, k2⟩ := Subgroup.mem_inf.1 hk
    exact congrFun (hψK k k1 ((f5 k k1).1 k2)) t
  have hψsum : ∀ s, ψ s = ∑ g ∈ c.support, c g * f (φ (s * g)) := by
    intro s
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    rfl
  have key : ∀ t, (Fintype.card (K ⧸ K') : ℂ) * ψ t = ∑ g ∈ c.support, c g * f (A g (t * y g)) := by
    intro t
    have e1 : (Fintype.card (K ⧸ K') : ℂ) * ψ t = ∑ q : K ⧸ K', ψ (t * rep q) := by
      rw [Finset.sum_congr rfl fun q _ => hψfix _ (hrepK q) t, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [e1, Finset.sum_congr rfl fun q _ => hψsum _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.mul_sum, map_sum]
    refine congrArg (c g * ·) (Finset.sum_congr rfl fun q _ => ?_)
    have hm : (rep q * x g) * y g = y g * (rep q * x g) :=
      f1 _ ((locU n w).mul_mem (hrepl q) (hx g)) _ (hy g)
    show f (φ (t * rep q * g)) = f (φ (t * y g * rep q * x g))
    congr 2
    calc t * rep q * g = t * ((rep q * x g) * y g) := by
          conv_lhs => rw [hxy g]
          simp only [mul_assoc]
      _ = t * y g * rep q * x g := by rw [hm]; simp only [mul_assoc]
  by_cases hall : ∀ g ∈ c.support, A g = 0
  · exfalso
    have hcard : (Fintype.card (K ⧸ K') : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨(QuotientGroup.mk 1 : K ⧸ K')⟩).ne'
    refine hψ0 (funext fun t => ?_)
    have h := key t
    rw [Finset.sum_eq_zero fun g hg => by rw [hall g hg]; simp] at h
    exact (mul_eq_zero.1 h).resolve_left hcard
  · push_neg at hall
    obtain ⟨g, hg, hne⟩ := hall
    refine ⟨A g, hne, ?_, ?_⟩
    · have e : A g = ∑ q : K ⧸ K', fun t => φ (t * (rep q * x g)) := by
        funext t
        simp only [A, φg, Finset.sum_apply, mul_assoc]
      unfold InSpan
      rw [e]
      exact Submodule.sum_mem _ fun q _ =>
        Submodule.subset_span ⟨_, (locU n w).mul_mem (hrepl q) (hx g), rfl⟩
    · intro k hk t
      exact sum_translate K K' (φg g) (fun s m hm => hUf g _ (Subgroup.mem_iInf.1
        (Subgroup.mem_iInf.1 (Subgroup.mem_subgroupOf.1 hm) g) hg) s) k hk t
