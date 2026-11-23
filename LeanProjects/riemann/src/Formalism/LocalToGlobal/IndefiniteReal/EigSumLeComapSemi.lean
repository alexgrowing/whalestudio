import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapPowSub

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {K : Type} [Field K] {σ : K →+* ℂ}

def cxSys {I : Type} (σ : K →+* ℂ) (C : (I → K) → Prop) : (I → ℂ) → Prop :=
  fun y => ∃ x, C x ∧ y = fun i => σ (x i)

variable {V E : Type} [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]

theorem map_pow_sub (f : V →ₛₗ[σ] E) (T : Module.End K V) (S : Module.End ℂ E)
    (h : ∀ v, f (T v) = S (f v)) (a : K) (k : ℕ) (v : V) :
    f (((T - a • 1) ^ k) v) = ((S - σ a • 1) ^ k) (f v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smulₛₗ, h]

theorem map_maxGen (f : V →ₛₗ[σ] E) {T : Module.End K V} {S : Module.End ℂ E}
    (h : ∀ v, f (T v) = S (f v)) {a : K} {v : V} (hv : v ∈ T.maxGenEigenspace a) :
    f v ∈ S.maxGenEigenspace (σ a) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  exact ⟨k, by rw [← map_pow_sub f T S h a k v, hk, map_zero]⟩

variable {I : Type}

theorem map_eigAt (f : V →ₛₗ[σ] E) {op : I → Module.End K V} {h : I → Module.End ℂ E}
    (hf : ∀ i v, f (op i v) = h i (f v)) {x : I → K} {v : V} (hv : v ∈ eigAt op x) :
    f v ∈ eigAt h (fun i => σ (x i)) := by
  unfold eigAt at hv ⊢
  rw [Submodule.mem_iInf] at hv ⊢
  exact fun i => map_maxGen f (hf i) (hv i)

theorem eigSum_le_comap_semi (f : V →ₛₗ[σ] E) {op : I → Module.End K V} {h : I → Module.End ℂ E}
    (hf : ∀ i v, f (op i v) = h i (f v)) (C : (I → K) → Prop) :
    eigSum op C ≤ (eigSum h (cxSys σ C)).comap f := by
  show (⨆ (x : I → K) (_ : C x), eigAt op x) ≤ _
  refine iSup₂_le fun x hx => ?_
  intro v hv
  rw [Submodule.mem_comap]
  exact eigAt_le_eigSum (op := h) ⟨x, hx, rfl⟩ (map_eigAt f hf hv)

theorem mem_eigSum_iff_map [FiniteDimensional K V] [FiniteDimensional ℂ E] (f : V →ₛₗ[σ] E)
    {op : I → Module.End K V} (hc : PairComm op) (hs : SplitOver op)
    {h : I → Module.End ℂ E} (hch : PairComm h) (hf : ∀ i v, f (op i v) = h i (f v))
    {Z : Submodule K V} (hZ : ∀ i, Z ≤ Z.comap (op i)) (hinj : ∀ z ∈ Z, f z = 0 → z = 0)
    (C : (I → K) → Prop) {v : V} (hv : v ∈ Z) :
    v ∈ eigSum op C ↔ f v ∈ eigSum h (cxSys σ C) := by
  constructor
  · intro hv'
    exact eigSum_le_comap_semi f hf C hv'
  · intro hfv
    have hpv : eigProj hc hs C v ∈ eigSum op C := eigProj_apply_mem hc hs C v
    have h2 : v - eigProj hc hs C v ∈ eigSum op (fun x => ¬ C x) := sub_eigProj_mem hc hs C v
    have hZ2 : v - eigProj hc hs C v ∈ Z := Z.sub_mem hv (eigProj_mem_of_stable hc hs C hZ hv)
    have hf1 : f (v - eigProj hc hs C v) ∈ eigSum h (cxSys σ C) := by
      rw [map_sub]
      exact Submodule.sub_mem _ hfv (eigSum_le_comap_semi f hf C hpv)
    have hf2 : f (v - eigProj hc hs C v) ∈ eigSum h (cxSys σ fun x => ¬ C x) :=
      eigSum_le_comap_semi f hf _ h2
    have hdis : Disjoint (eigSum h (cxSys σ C)) (eigSum h (cxSys σ fun x => ¬ C x)) := by
      apply disjoint_eigSum hch
      rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx⟩
      apply hx'
      have e : x' = x := funext fun i => (σ.injective (congrFun hxx i)).symm
      rw [e]
      exact hx
    have h0 : f (v - eigProj hc hs C v) = 0 := (Submodule.disjoint_def.1 hdis) _ hf1 hf2
    have e := hinj _ hZ2 h0
    rw [sub_eq_zero] at e
    rw [e]
    exact hpv

theorem inj_of_li {ι : Type*} (b : Basis ι K V) (f : V →ₛₗ[σ] E)
    (h : LinearIndependent ℂ fun k => f (b k)) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun v hv => ?_
  have e := b.linearCombination_repr v
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at e
  have h3 : ∑ i ∈ (b.repr v).support, σ (b.repr v i) • f (b i) = f v := by
    rw [← congrArg f e, map_sum]
    simp only [map_smulₛₗ]
  have hall := linearIndependent_iff'.1 h _ _ (h3.trans hv)
  have hr : b.repr v = 0 := by
    ext i
    by_contra hi
    exact hi (σ.injective ((hall i (Finsupp.mem_support_iff.2 hi)).trans (map_zero σ).symm))
  simpa using congrArg b.repr.symm hr

end Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem theta_jR_inj (hR : X.KFormR) (t : Bs.Tup) (z : A.FR t) (hz : z ∈ X.Z t)
    (h0 : X.Θ t (X.jR t z) = 0) : z = 0 := by
  simp only [CxData.Z, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  have h1 : X.jR t z = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hw, LinearMap.adjoint_inner_left, hw, h0, inner_zero_right]
  exact inj_of_li (bR (A := A) t) (X.jR t) (hR t).1 (h1.trans (map_zero _).symm)

theorem theta_jL_inj (hL : X.KFormL) (j : Bs.J) (t : Bs.Tup) (z : A.FL j t) (hz : z ∈ X.Zl j t)
    (h0 : X.θ' j t (X.jL j t z) = 0) : z = 0 := by
  simp only [CxData.Zl, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  have h1 : X.jL j t z = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hw, LinearMap.adjoint_inner_left, hw, h0, inner_zero_right]
  exact inj_of_li (bL (A := A) j t) (X.jL j t) (hL j t).1 (h1.trans (map_zero _).symm)

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem iC_cpt_eq (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • Pi.single k (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, map_smulₛₗ, CxData.iC, lin, Fintype.linearCombination_apply, cpt]

theorem tC_cpt_eq (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding x) = X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) := by
  have hx : x = ∑ k, x k • Pi.single k (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, map_smulₛₗ, CxData.tC, lin, Fintype.linearCombination_apply, cpt]

end CxData

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

structure HeckeThetaR (hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE) : Prop where

  intw : ∀ t i (u : X.FC t), X.Θ t (X.opC t (Sum.inl i) u) = hE t i (X.Θ t u)

  comm : PairComm (hE A.fam.μ0)

  parts : ∀ p : A.fam.base.Ix,
    X.EEp p = eigSum (hE A.fam.μ0) (cxSys A.fam.base.v0.embedding ((A.fam.R A.fam.μ0).HasRes p.1))

structure HeckeThetaL (hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)) : Prop where

  intw : ∀ j t i (u : X.FLC j t), X.θ' j t (X.opLC j t (Sum.inl i) u) = hW j t i (X.θ' j t u)

  comm : ∀ j, PairComm (hW j A.fam.μ0)

  parts : ∀ (j : Fin m) (p : A.fam.base.Ix),
    X.Wp j p = eigSum (hW j A.fam.μ0)
      (cxSys A.fam.base.v0.embedding ((A.fam.L j A.fam.μ0).HasRes (A.fam.tr j p.1)))

variable {A X}

theorem kerStabR_hecke {hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE} (hH : HeckeThetaR A X hE)
    (t : T) (i : (A.fam.R t).Pl × ℕ) (u : X.FC t) (hu : X.Θ t u = 0) :
    X.Θ t (X.opC t (Sum.inl i) u) = 0 := by
  rw [hH.intw, hu, map_zero]

theorem kerStabL_hecke {hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)} (hH : HeckeThetaL A X hW)
    (j : Fin m) (t : T) (i : (A.fam.L j t).Pl × ℕ) (u : X.FLC j t) (hu : X.θ' j t u = 0) :
    X.θ' j t (X.opLC j t (Sum.inl i) u) = 0 := by
  rw [hH.intw, hu, map_zero]

theorem kerStabR_of {hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE} (hH : HeckeThetaR A X hE)
    (hG : ∀ t (g : G) (u : X.FC t), X.Θ t u = 0 → X.Θ t (X.opC t (Sum.inr g) u) = 0) : X.KerStabR := by
  intro t i u hu
  rcases i with i | g
  · exact kerStabR_hecke hH t i u hu
  · exact hG t g u hu

theorem kerStabL_of {hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)} (hH : HeckeThetaL A X hW)
    (hG : ∀ j t (g : G) (u : X.FLC j t), X.θ' j t u = 0 → X.θ' j t (X.opLC j t (Sum.inr g) u) = 0) :
    X.KerStabL := by
  intro j t i u hu
  rcases i with i | g
  · exact kerStabL_hecke hH j t i u hu
  · exact hG j t g u hu

theorem toF_mem_Z {B : BlockDat K G Pl0} (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ Z := by
  have h1 : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
    rw [BlockDat.zE, subE_mulVec]
    exact Submodule.coe_mem _
  simp only [BlockDat.Z0, BlockDat.inV0, BlockDat.coord, Submodule.mem_comap, Submodule.mem_map,
    Matrix.mulVecLin_apply] at h1
  obtain ⟨w, hw, hwe⟩ := h1
  have e : B.toF ℓ Z y = w := by
    simp only [BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply]
    rw [← hwe]
    simp
  rw [e]
  exact hw

theorem part_iff_rows (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A.fam.Ok s)
    {hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE} (hH : HeckeThetaR A X hE) (p : A.fam.base.Ix)
    (ℓ : Lvl K G) (y : Fin ((A.fam.R A.fam.μ0).dZ ℓ (X.Z A.fam.μ0)) → K) :
    y ∈ (A.fam.R A.fam.μ0).part ℓ (X.Z A.fam.μ0) p.1 ↔
      X.Θ A.fam.μ0 (X.jR A.fam.μ0 ((A.fam.R A.fam.μ0).toF ℓ (X.Z A.fam.μ0) y)) ∈ X.EEp p := by
  have hB := hOk.what₂ A.fam.μ0
  have hZ : ∀ i, X.Z A.fam.μ0 ≤ (X.Z A.fam.μ0).comap ((A.fam.R A.fam.μ0).op i) := fun i =>
    Submodule.map_le_iff_le_comap.1 (hst.1 A.fam.μ0 (Sum.inl i))
  have hmemZ := toF_mem_Z ℓ (X.Z A.fam.μ0) y
  have e1 : y ∈ (A.fam.R A.fam.μ0).part ℓ (X.Z A.fam.μ0) p.1 ↔
      (A.fam.R A.fam.μ0).toF ℓ (X.Z A.fam.μ0) y ∈ (A.fam.R A.fam.μ0).partF p.1 := by
    simp only [BlockDat.part, BlockDat.inV0, BlockDat.coord, Submodule.mem_comap, Submodule.mem_map,
      BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨w, hw, hwe⟩
      rw [← hwe, LinearEquiv.symm_apply_apply]
      exact hw
    · intro h
      exact ⟨_, h, LinearEquiv.apply_symm_apply _ _⟩
  rw [e1, hH.parts p]
  exact mem_eigSum_iff_map ((X.Θ A.fam.μ0).comp (X.jR A.fam.μ0)) hB.comm hB.split hH.comm
    (fun i v => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        show (A.fam.R A.fam.μ0).op i v = A.fam.amb.opR A.fam.μ0 (Sum.inl i) v from rfl,
        X.jR_opR hR, hH.intw])
    hZ (fun z hz h0 => X.theta_jR_inj hR _ z hz h0) _ hmemZ

theorem part_iff_lifts (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A.fam.Ok s)
    {hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)} (hH : HeckeThetaL A X hW) (j : Fin m)
    (p : A.fam.base.Ix) (ℓ : Lvl K G) (y : Fin ((A.fam.L j A.fam.μ0).dZ ℓ (X.Zl j A.fam.μ0)) → K) :
    y ∈ (A.fam.L j A.fam.μ0).part ℓ (X.Zl j A.fam.μ0) (A.fam.tr j p.1) ↔
      X.θ' j A.fam.μ0 (X.jL j A.fam.μ0 ((A.fam.L j A.fam.μ0).toF ℓ (X.Zl j A.fam.μ0) y)) ∈ X.Wp j p := by
  have hB := hOk.lifts j A.fam.μ0
  have hZ : ∀ i, X.Zl j A.fam.μ0 ≤ (X.Zl j A.fam.μ0).comap ((A.fam.L j A.fam.μ0).op i) := fun i =>
    Submodule.map_le_iff_le_comap.1 (hst.2 j A.fam.μ0 (Sum.inl i))
  have hmemZ := toF_mem_Z ℓ (X.Zl j A.fam.μ0) y
  have e1 : y ∈ (A.fam.L j A.fam.μ0).part ℓ (X.Zl j A.fam.μ0) (A.fam.tr j p.1) ↔
      (A.fam.L j A.fam.μ0).toF ℓ (X.Zl j A.fam.μ0) y ∈ (A.fam.L j A.fam.μ0).partF (A.fam.tr j p.1) := by
    simp only [BlockDat.part, BlockDat.inV0, BlockDat.coord, Submodule.mem_comap, Submodule.mem_map,
      BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨w, hw, hwe⟩
      rw [← hwe, LinearEquiv.symm_apply_apply]
      exact hw
    · intro h
      exact ⟨_, h, LinearEquiv.apply_symm_apply _ _⟩
  rw [e1, hH.parts j p]
  exact mem_eigSum_iff_map ((X.θ' j A.fam.μ0).comp (X.jL j A.fam.μ0)) hB.comm hB.split (hH.comm j)
    (fun i v => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        show (A.fam.L j A.fam.μ0).op i v = A.fam.amb.opL j A.fam.μ0 (Sum.inl i) v from rfl,
        X.jL_opL hL, hH.intw])
    hZ (fun z hz h0 => X.theta_jL_inj hL j _ z hz h0) _ hmemZ

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

theorem equivRows_of (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A.fam.Ok s)
    {hE : ∀ t, (A.fam.R t).Pl × ℕ → Module.End ℂ X.EE} (hH : HeckeThetaR A X hE) (b : Bool) :
    X.H3 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro p x
  rw [X.iC_cpt_eq]
  cases b
  · exact part_iff_rows hR hst hOk hH p (A.fam.lvl P0 ψ0) x
  · exact part_iff_rows hR hst hOk hH p (A.fam.lvl P1 ψ1) x

theorem equivLifts_of (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A.fam.Ok s)
    {hW : ∀ j t, (A.fam.L j t).Pl × ℕ → Module.End ℂ (X.W j)} (hH : HeckeThetaL A X hW) (b : Bool) :
    X.H3W (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j p x
  rw [X.tC_cpt_eq]
  cases b
  · exact part_iff_lifts hL hst hOk hH j p (A.fam.lvlA P0 ψ0) x
  · exact part_iff_lifts hL hst hOk hH j p (A.fam.lvlA P1 ψ1) x

end Concrete

end Formalism.IndefR.Cx
