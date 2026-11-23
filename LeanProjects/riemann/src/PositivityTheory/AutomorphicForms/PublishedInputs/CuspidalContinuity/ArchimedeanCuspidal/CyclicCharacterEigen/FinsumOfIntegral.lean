import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspSSDB
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.CoeSmEqSymm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.MemIffLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PsiLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolRep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QdetMemAdjSub

noncomputable section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Af Matrix

namespace Ad3P.CuspidalityAtInfinity

section Qdet

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

def interSub (S : M →ₗ[ℂ] N) : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ N) where
  carrier := {p | ∀ m, p.2 (S m) = S (p.1 m)}
  mul_mem' {p q} hp hq m := by
    change p.2 (q.2 (S m)) = S (p.1 (q.1 m))
    rw [hq, hp]
  add_mem' {p q} hp hq m := by
    change p.2 (S m) + q.2 (S m) = S (p.1 m + q.1 m)
    rw [hp, hq, map_add]
  algebraMap_mem' c m := by
    change (algebraMap ℂ (Module.End ℂ N) c) (S m) = S ((algebraMap ℂ (Module.End ℂ M) c) m)
    simp [Module.algebraMap_end_apply]

theorem qdet_inter {n : ℕ} (S : M →ₗ[ℂ] N) (D : Fin n → Fin n → Module.End ℂ M) (E : Fin n → Fin n → Module.End ℂ N)
    (h : ∀ i j m, E i j (S m) = S (D i j m)) (u : ℂ) (m : M) :
    Formalism.REAL.qdet E u (S m) = S (Formalism.REAL.qdet D u m) := by
  set P : Fin n → Fin n → interSub S := fun i j => ⟨(D i j, E i j), fun m => h i j m⟩
  have h1 := PI.UnitaryGroupMassFormula.DSIC.qdet_map (interSub S).val P u
  have h2 := PI.UnitaryGroupMassFormula.DSIC.qdet_map (AlgHom.fst ℂ (Module.End ℂ M) (Module.End ℂ N)) (fun a b => (D a b, E a b)) u
  have h3 := PI.UnitaryGroupMassFormula.DSIC.qdet_map (AlgHom.snd ℂ (Module.End ℂ M) (Module.End ℂ N)) (fun a b => (D a b, E a b)) u
  have hm := (Formalism.REAL.qdet P u).2 m
  have e : ((Formalism.REAL.qdet P u : interSub S) : Module.End ℂ M × Module.End ℂ N) =
      Formalism.REAL.qdet (fun a b => (D a b, E a b)) u := h1
  rw [e] at hm
  have e1 : (Formalism.REAL.qdet (fun a b => (D a b, E a b)) u).1 = Formalism.REAL.qdet D u := h2
  have e2 : (Formalism.REAL.qdet (fun a b => (D a b, E a b)) u).2 = Formalism.REAL.qdet E u := h3
  rw [e1, e2] at hm
  exact hm

end Qdet

section Bridge

open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

theorem Eop_eq (v : InfinitePlace ℚ) (i j : Fin 3) :
    TR.Eop (E := ℚ) (a := 3) v i j = TR.lie ℚ 3 (TR.toL (Matrix.single i j 1)) := by
  unfold TR.Eop
  congr 3
  funext w
  rw [Subsingleton.elim w v]
  simp

theorem lieEq_single (i j : Fin 3) :
    Fb.lieEq ℚ 3 (TR.toL (Matrix.single i j 1)) =
      (⟨(Matrix.single i j 1 : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ)), Submodule.mem_top⟩ :
        (isExpLieAlgebra ℚ 3).lieSubalgebra) := by
  refine Subtype.ext ?_
  rw [Fb.coe_lieEq]
  refine Matrix.ext fun a b => ?_
  rw [Fb.matEq_apply]
  change Fb.mixEq ℚ ((Matrix.single i j (1 : TR.Rinf ℚ)) a b) = (Matrix.single i j (1 : mixedEmbedding.mixedSpace ℚ)) a b
  simp only [Matrix.single_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem EA_eq (i j : Fin 3) :
    Ad3.EA i j = uAction (UniversalEnvelopingAlgebra.ι ℝ (Fb.lieEq ℚ 3 (TR.toL (Matrix.single i j 1)))) := by
  rw [lieEq_single]
  rfl

theorem smEq_Eop (v : InfinitePlace ℚ) (i j : Fin 3) (φ : TR.Sm ℚ 3) :
    Fb.smEq ℚ 3 (TR.Eop v i j φ) = Ad3.EA i j (Fb.smEq ℚ 3 φ) := by
  rw [EA_eq, Fb.uAction_ι_smEq, Eop_eq v]

theorem cap_eq (v : InfinitePlace ℚ) (u : ℂ) :
    TR.cap (E := ℚ) (a := 3) v u = Formalism.REAL.qdet (TR.Eop (E := ℚ) (a := 3) v) (u + 1) := by
  rw [TR.cap]
  norm_num

theorem oneL_eq : TR.oneL ℚ 3 = ∑ i : Fin 3, TR.toL (Matrix.single i i 1) := by
  have h : (1 : Matrix (Fin 3) (Fin 3) (TR.Rinf ℚ)) = ∑ i : Fin 3, Matrix.single i i 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_three]
  change TR.toL 1 = _
  rw [h]
  rfl

theorem lie_oneL (v : InfinitePlace ℚ) : TR.lie ℚ 3 (TR.oneL ℚ 3) = ∑ i : Fin 3, TR.Eop v i i := by
  rw [oneL_eq, map_sum]
  simp only [Eop_eq v]

variable {V : Submodule ℂ (Ad3.G3 → ℂ)} (hV : Ad3.WhA V)

def incl : V →ₗ[ℂ] archSmooth ℚ 3 where
  toFun W := ⟨W.1, hV.arch W.1 W.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem incl_injective : Function.Injective (incl hV) := fun x y h => by
  have h' : x.1 = y.1 := congrArg (fun f : archSmooth ℚ 3 => (f : Ad3.G3 → ℂ)) h
  exact Subtype.ext h'

def DV (i j : Fin 3) : Module.End ℂ V :=
  LinearMap.codRestrict V ((archSmooth ℚ 3).subtype ∘ₗ Ad3.EA i j ∘ₗ incl hV) fun W => hV.lie _ W.2 i j

theorem incl_DV (i j : Fin 3) (W : V) : incl hV (DV hV i j W) = Ad3.EA i j (incl hV W) := rfl

theorem cap_form (k : ℕ)
    (hcap : ∀ W (hW : W ∈ V) (u : ℂ), Formalism.REAL.qdet Ad3.EA (u + 1) ⟨W, hV.arch W hW⟩ =
      ((u + (k - 1)) * u * (u - (k - 1))) • (⟨W, hV.arch W hW⟩ : archSmooth ℚ 3))
    (U : V →ₗ[ℂ] archSmooth ℚ 3) (hU : ∀ (W : V) i j, U ⟨_, hV.lie _ W.2 i j⟩ = Ad3.EA i j (U W))
    (W : V) (v : InfinitePlace ℚ) (u : ℂ) :
    TR.cap v u ((Fb.smEq ℚ 3).symm (U W)) = ((u + (k - 1)) * u * (u - (k - 1))) • (Fb.smEq ℚ 3).symm (U W) := by
  set c : ℂ := (u + (k - 1)) * u * (u - (k - 1))
  have h1 : Formalism.REAL.qdet (DV hV) (u + 1) W = c • W := by
    refine incl_injective hV ?_
    rw [← qdet_inter (incl hV) (DV hV) Ad3.EA (fun i j m => (incl_DV hV i j m).symm), map_smul]
    exact hcap W.1 W.2 u
  have h2 : Formalism.REAL.qdet Ad3.EA (u + 1) (U W) = c • U W := by
    rw [qdet_inter U (DV hV) Ad3.EA (fun i j m => (hU m i j).symm), h1, map_smul]
  refine (Fb.smEq ℚ 3).injective ?_
  rw [cap_eq, map_smul, LinearEquiv.apply_symm_apply]
  have h3 := qdet_inter (Fb.smEq ℚ 3).toLinearMap (TR.Eop v) Ad3.EA (fun i j m => (smEq_Eop v i j m).symm) (u + 1)
    ((Fb.smEq ℚ 3).symm (U W))
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h3
  rw [← h3, h2]

theorem trace_form (htr : ∀ W (hW : W ∈ V), (∑ i, Ad3.EA i i) ⟨W, hV.arch W hW⟩ = 0)
    (U : V →ₗ[ℂ] archSmooth ℚ 3) (hU : ∀ (W : V) i j, U ⟨_, hV.lie _ W.2 i j⟩ = Ad3.EA i j (U W)) (W : V) :
    TR.lie ℚ 3 (TR.oneL ℚ 3) ((Fb.smEq ℚ 3).symm (U W)) = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  have h1 : ∑ i, DV hV i i W = 0 := by
    refine incl_injective hV ?_
    rw [map_sum, map_zero]
    simp only [incl_DV]
    rw [← LinearMap.sum_apply]
    exact htr W.1 W.2
  refine (Fb.smEq ℚ 3).injective ?_
  rw [lie_oneL v, LinearMap.sum_apply, map_sum, map_zero]
  simp only [smEq_Eop, LinearEquiv.apply_symm_apply]
  rw [← Finset.sum_congr rfl fun i _ => hU W i i, ← map_sum]
  convert map_zero U
  exact h1

end Bridge

section Local

open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic

section General

open MeasureTheory GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra
open scoped ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem esymm_eq (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) = ((Finset.univ.val.map z).map fun b : ℂˣ => (b : ℂ)).esymm r := by
  rw [evalAt_esymmL, Multiset.map_map, Finset.esymm_map_val]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomialChar_apply]
  simp only [lamS, Function.comp_apply]
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [hi]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

private theorem finsum_of_integral (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F)
    (h : ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) ∂μ =
      evalAt z (satakeTransform μ (minusculeHecke μ r)) * f g) :
    ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out * f (g * c.out) =
        sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f g := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have hcs : HasCompactSupport fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * f (g * x) := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs (fun x k hk => by
      rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk]),
    Complex.real_smul, evalAt_satakeTransform_minusculeHecke z hr, mul_assoc, mul_assoc] at h
  have h2 := mul_left_cancel₀ hK h
  rw [← mul_assoc] at h2
  exact h2

end General

open scoped ValuativeRel

private theorem psi_eq (w : Ad3.Pl) (x : Ad3.Qv w) :
    (Circle.coeHom.compAddChar (localAdelicChar ℚ w)) x = UpperTheory.V.Af.Smo.psiL w x := rfl

private theorem hpsi0 (w : Ad3.Pl) (hg : UpperTheory.V.Af.Smo.GoodAt w (UpperTheory.V.Af.Smo.psiL w)) :
    ∀ x ∈ 𝒪[Ad3.Qv w], (Circle.coeHom.compAddChar (localAdelicChar ℚ w)) x = 1 := fun x hx => by
  rw [psi_eq]
  exact hg.1 x ((GroundTheory.Global.mem_valuationInteger_iff w x).1 hx)

theorem sph_inv (w : Ad3.Pl) (hg : UpperTheory.V.Af.Smo.GoodAt w (UpperTheory.V.Af.Smo.psiL w)) (ν : (Ad3.Qv w)ˣ →* ℂˣ)
    (x : GL (Fin 3) (Ad3.Qv w)) {k : GL (Fin 3) (Ad3.Qv w)} (hk : k ∈ GlobalTheory.LFun.KGL w 3) :
    Ad3.sphW (localAdelicChar ℚ w) ν (x * k) = Ad3.sphW (localAdelicChar ℚ w) ν x := by
  have hK := (UpperTheory.V.Af.Smo.sphDict ℚ 3 w).1
  rw [← hK] at hk
  exact Spherical.sphericalWhittaker_mul_right (hpsi0 w hg) _ x hk

theorem sph_eig (w : Ad3.Pl) (hg : UpperTheory.V.Af.Smo.GoodAt w (UpperTheory.V.Af.Smo.psiL w)) (ν : (Ad3.Qv w)ˣ →* ℂˣ)
    (j : ℕ) (hj : j ≤ 3) (x : GL (Fin 3) (Ad3.Qv w)) :
    ∑ᶠ c : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3,
      Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (GLnLocal.uniformizer (Ad3.Qv w) : Ad3.Qv w) j c.out *
        Ad3.sphW (localAdelicChar ℚ w) ν (x * c.out) =
      GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 {ν (unifUnit (Ad3.Qv w)), 1, (ν (unifUnit (Ad3.Qv w)))⁻¹} j *
        Ad3.sphW (localAdelicChar ℚ w) ν x := by
  obtain ⟨hK, hu, hq, -⟩ := UpperTheory.V.Af.Smo.sphDict ℚ 3 w
  set z : Fin 3 → ℂˣ := ![ν (unifUnit (Ad3.Qv w)), 1, (ν (unifUnit (Ad3.Qv w)))⁻¹] with hz
  have hB : ({ν (unifUnit (Ad3.Qv w)), 1, (ν (unifUnit (Ad3.Qv w)))⁻¹} : Multiset ℂˣ) = Finset.univ.val.map z := by
    rw [Fin.univ_val_map]
    rfl
  have hψ₁ : ∃ y : Ad3.Qv w, (GLnLocal.uniformizer (Ad3.Qv w) : Ad3.Qv w) * y ∈ 𝒪[Ad3.Qv w] ∧
      (Circle.coeHom.compAddChar (localAdelicChar ℚ w)) y ≠ 1 := by
    obtain ⟨y, hy, hy'⟩ := hg.2 _ hu
    exact ⟨y, (GroundTheory.Global.mem_valuationInteger_iff w _).2 hy, hy'⟩
  borelize (GL (Fin 3) (Ad3.Qv w))
  let μ : MeasureTheory.Measure (GL (Fin 3) (Ad3.Qv w)) := MeasureTheory.Measure.haar
  have h1 := Spherical.integral_minusculeHecke_mul_sphericalWhittaker (μ := μ) (hpsi0 w hg) hψ₁ z hj x
  have h2 := finsum_of_integral (μ := μ) z (fun g k hk => Spherical.sphericalWhittaker_mul_right (hpsi0 w hg) z g hk) hj x h1
  rw [hK, ← UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict ℚ 3 w j hj, hq j hj, esymm_eq] at h2
  rw [hB, GlobalTheory.LFun.satEig]
  exact h2

end Local

section Local2

open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic

open GlobalTheory.CuspRep in
private theorem finAt_finGL_locGL (w v : Ad3.Pl) (y : GL (Fin 3) (Ad3.Qv w)) :
    Reduction.finAt v (finGL ℚ 3 (locGL ℚ 3 w y)) = Matrix.GeneralLinearGroup.map (pLoc ℚ v) (locGL ℚ 3 w y) := by
  have h := map_cornerGL_of_hom (sFin ℚ) (pFin ℚ) (RingHom.id _) (fun _ => rfl) (locGL ℚ 3 w y)
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  have h2 := congrArg (fun M : GL (Fin 3) (Af ℚ) => (M : Matrix (Fin 3) (Fin 3) (Af ℚ)) a b) h
  rw [Reduction.finAt_apply]
  change (((finGL ℚ 3 (locGL ℚ 3 w y) : GL (Fin 3) (Ad ℚ)) : Matrix (Fin 3) (Fin 3) (Ad ℚ)) a b).2 v =
    pLoc ℚ v (((locGL ℚ 3 w y : GL (Fin 3) (Af ℚ)) : Matrix (Fin 3) (Fin 3) (Af ℚ)) a b)
  have h3 : (((finGL ℚ 3 (locGL ℚ 3 w y) : GL (Fin 3) (Ad ℚ)) : Matrix (Fin 3) (Fin 3) (Ad ℚ)) a b).2 =
      ((locGL ℚ 3 w y : GL (Fin 3) (Af ℚ)) : Matrix (Fin 3) (Fin 3) (Af ℚ)) a b := h2
  rw [h3]
  rfl

open GlobalTheory.CuspRep in
private theorem infAt_finGL (v : InfinitePlace ℚ) (k : GL (Fin 3) (Af ℚ)) :
    Reduction.infAt v (finGL ℚ 3 k) = 1 := by
  have h := map_cornerGL_of_zero (sFin ℚ) (RingHom.fst (InfiniteAdeleRing ℚ) (Af ℚ)) (fun _ => rfl) k
  rw [← Reduction.infAt_one (K := ℚ) (n := 3) v]
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  have h2 := congrArg (fun M : GL (Fin 3) (InfiniteAdeleRing ℚ) => (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b) h
  rw [Reduction.infAt_apply, Reduction.infAt_apply]
  have h3 : (((finGL ℚ 3 k : GL (Fin 3) (Ad ℚ)) : Matrix (Fin 3) (Fin 3) (Ad ℚ)) a b).1 =
      ((1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b := h2
  change (((finGL ℚ 3 k : GL (Fin 3) (Ad ℚ)) : Matrix (Fin 3) (Fin 3) (Ad ℚ)) a b).1 v = _
  rw [h3]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

theorem isLoc_locGL (w : Ad3.Pl) (y : GL (Fin 3) (Ad3.Qv w)) :
    Ad3.IsLoc w y (GlobalTheory.CuspRep.finGL ℚ 3 (GlobalTheory.CuspRep.locGL ℚ 3 w y)) :=
  ⟨(finAt_finGL_locGL w w y).trans (GlobalTheory.CuspRep.pLoc_locGL w y),
    fun v' hv => (finAt_finGL_locGL w v' y).trans (GlobalTheory.CuspRep.pLoc_locGL_of_ne hv y),
    fun v => infAt_finGL v _⟩

theorem sph_transl (D : Ad3.Dat) (w : Ad3.Pl) (W : Ad3.G3 → ℂ) (hs : Ad3.SphAt D w W) (g : Ad3.G3) :
    ∃ (g1 : Ad3.G3) (x1 : GL (Fin 3) (Ad3.Qv w)), ∀ y : GL (Fin 3) (Ad3.Qv w),
      W (g * GlobalTheory.CuspRep.finGL ℚ 3 (GlobalTheory.CuspRep.locGL ℚ 3 w y)) =
        W g1 * Ad3.sphW (localAdelicChar ℚ w) (D.ν w) (x1 * y) := by
  set x0 := Reduction.finAt w g
  set e : Ad3.G3 := GlobalTheory.CuspRep.finGL ℚ 3 (GlobalTheory.CuspRep.locGL ℚ 3 w x0)
  have he : Reduction.finAt w e = x0 := (isLoc_locGL w x0).1
  have hinv : Reduction.finAt w e⁻¹ = x0⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← he, ← Reduction.finAt_mul, mul_inv_cancel, Reduction.finAt_one]
  refine ⟨g * e⁻¹, x0, fun y => ?_⟩
  have h1 : Reduction.finAt w (g * e⁻¹) = 1 := by
    rw [Reduction.finAt_mul, hinv, mul_inv_cancel]
  have h2 : g * GlobalTheory.CuspRep.finGL ℚ 3 (GlobalTheory.CuspRep.locGL ℚ 3 w y) =
      g * e⁻¹ * GlobalTheory.CuspRep.finGL ℚ 3 (GlobalTheory.CuspRep.locGL ℚ 3 w (x0 * y)) := by
    rw [map_mul, map_mul, mul_assoc, inv_mul_cancel_left]
  rw [h2]
  exact hs _ h1 _ _ (isLoc_locGL w (x0 * y))

end Local2

section HolRepCopy

open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Sd
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin locGL finGL GA chiDet)

section Proj
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem stable_iSup (S : Set (TR.CuspSub F a)) : TR.IsStable (⨆ π ∈ S, π.V) := fun o φ hφ => by
  refine Submodule.mem_comap.1 ((iSup₂_le (a := Submodule.comap (TR.act o) _) fun π hπ x hx => ?_) hφ)
  exact Submodule.mem_iSup_of_mem π (Submodule.mem_iSup_of_mem hπ (π.stable o x hx))

private theorem proj {φ : TR.Sm F a} (h0 : φ ≠ 0) (h : φ ∈ ⨆ π : TR.CuspSub F a, π.V) :
    ∃ (π : TR.CuspSub F a) (ψ : TR.Sm F a), ψ ∈ π.V ∧ ψ ≠ 0 ∧ ∀ z : Module.End ℂ (TR.Sm F a),
      (∀ V, TR.IsStable V → ∀ x ∈ V, z x ∈ V) → ∀ c : ℂ, z φ = c • φ → z ψ = c • ψ := by
  classical
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.1 h
  induction S using Finset.induction_on with
  | empty => exact absurd (by simpa using hS) h0
  | insert π S hπ ih =>
    rw [Finset.iSup_insert] at hS
    have hs : TR.IsStable (⨆ π ∈ S, π.V) := stable_iSup (S : Set (TR.CuspSub F a))
    rcases π.irred (π.V ⊓ ⨆ π ∈ S, π.V) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, hs o x hx.2⟩) with e | e
    · obtain ⟨ψ, h1, ψ', h2, e2⟩ := Submodule.mem_sup.1 hS
      by_cases h3 : ψ = 0
      · exact ih (by rw [← e2, h3, zero_add]; exact h2)
      refine ⟨π, ψ, h1, h3, fun z hz c hc => ?_⟩
      rw [← e2, map_add, smul_add] at hc
      have h4 : z ψ - c • ψ ∈ π.V ⊓ ⨆ π ∈ S, π.V := by
        refine ⟨sub_mem (hz _ π.stable _ h1) (π.V.smul_mem c h1), ?_⟩
        have : z ψ - c • ψ = c • ψ' - z ψ' := by linear_combination (norm := module) hc
        rw [this]
        exact sub_mem (Submodule.smul_mem _ c h2) (hz _ hs _ h2)
      rw [e, Submodule.mem_bot] at h4
      exact sub_eq_zero.1 h4
    · exact ih ((sup_le (inf_eq_left.1 e) le_rfl) hS)

private theorem rt_lie (y : GL (Fin a) (TR.Rinf F)) (X : Matrix (Fin a) (Fin a) (TR.Rinf F)) :
    TR.rt F a (TR.infGL F a y) * TR.lie F a (TR.toL X) =
      TR.lie F a (TR.toL (y.val * X * (y⁻¹).val)) * TR.rt F a (TR.infGL F a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (TR.chart φ.1 (g * TR.infGL F a y)) (TR.oneL F a) (TR.toL X) =
    fderiv ℝ (TR.chart (fun x => φ.1 (x * TR.infGL F a y)) g) (TR.oneL F a) (TR.toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (TR.chart φ.1 g) (TR.toL y.val) :=
    (TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet y)).differentiableAt (by simp)
  have e1 : TR.lmul (TR.toL y.val) (TR.oneL F a) = TR.toL y.val := mul_one y.val
  have e2 : TR.rmul (TR.toL y.val) (TR.oneL F a) = TR.toL y.val := one_mul y.val
  rw [TR.chart_mul, TR.chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (TR.lmul (TR.toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (TR.rmul (TR.toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (TR.chart φ.1 g) (TR.toL y.val) (TR.toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm

open Classical in
private theorem lie_eq_sum (X : Matrix (Fin a) (Fin a) (TR.Rinf F)) :
    TR.lie F a (TR.toL X) = ∑ v, ∑ i, ∑ j, ((X i j v : ℝ) : ℂ) • TR.Eop v i j := by
  let L : Matrix (Fin a) (Fin a) (TR.Rinf F) →ₗ[ℝ] Module.End ℂ (TR.Sm F a) := TR.lie F a
  have e : X = ∑ v, ∑ i, ∑ j, X i j v • Matrix.single i j (Pi.single v 1 : TR.Rinf F) := by
    ext i j v
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Pi.single_apply, ite_apply]
  change L X = _
  conv_lhs => rw [e]
  simp only [map_sum, map_smul]
  rfl

private theorem rt_Eop (y : GL (Fin a) (TR.Rinf F)) (v : InfinitePlace F) (i j : Fin a) :
    TR.rt F a (TR.infGL F a y) * TR.Eop v i j =
      (∑ k, ∑ l, (((y.val k i v : ℝ) : ℂ) * (((y⁻¹).val j l v : ℝ) : ℂ)) • TR.Eop v k l) * TR.rt F a (TR.infGL F a y) := by
  classical
  rw [TR.Eop, rt_lie, lie_eq_sum, Finset.sum_eq_single v]
  · simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_apply]
  · intro v' _ h
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_apply, h]
  · simp

private theorem cap_act (v : InfinitePlace F) (u : ℂ) (o : TR.Op F a) : TR.act o * TR.cap v u = TR.cap v u * TR.act o := by
  cases o with
  | fin k => exact GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (fun i j => (TR.lie_rt_fin _ k).symm) _
  | cpt k =>
    set y := Unitary.toUnits k
    let f : TR.Rinf F →+* ℂ := Complex.ofRealHom.comp (Pi.evalRingHom _ v)
    have h := GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (rt_Eop y v) (u + ((a : ℂ) - 1) / 2)
    have hQP : ((y⁻¹).val.map f) * (y.val.map f) = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul]; simp
    exact h.trans (congrArg (· * _) (GlobalTheory.CapAdInv.qdet_ad _ (TR.glRel_Eop v) _ _ hQP (u + ((a : ℂ) - 1) / 2)))
  | lie X =>
    have h : ∀ v' i j, Commute (TR.Eop (a := a) v' i j) (TR.cap v u) := fun v' i j => by
      by_cases e : v' = v
      · subst e; exact (TR.cap_comm _ _ _ _).symm
      · exact GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (fun k l => TR.Eop_comm e _ _ _ _) _
    change Commute (TR.lie F a (TR.toL (Matrix.of X))) _
    rw [lie_eq_sum]
    exact Commute.sum_left _ _ _ fun v' _ => Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
      (h v' i j).smul_left _

private theorem cap_all (π : TR.CuspSub F a) {ψ : TR.Sm F a} (h : ψ ∈ π.V) (h0 : ψ ≠ 0) (v : InfinitePlace F) (u c : ℂ)
    (hc : TR.cap v u ψ = c • ψ) : ∀ x ∈ π.V, TR.cap v u x = c • x := by
  rcases π.irred (π.V ⊓ Module.End.eigenspace (TR.cap v u) c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← Module.End.mul_apply, ← cap_act, Module.End.mul_apply, this, map_smul]⟩) with e | e
  · exact absurd (e.le ⟨h, Module.End.mem_eigenspace_iff.2 hc⟩) h0
  · exact fun x hx => Module.End.mem_eigenspace_iff.1 (e.ge hx).2

private theorem exists_sat (P : Af.Hypotheses₂) (π : TR.CuspSub F a) (w : HeightOneSpectrum (𝓞 F))
    (h : HasFixed (π.locRep w) (GlobalTheory.LFun.KGL w a)) : ∃ B, π.HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, h2⟩ := locCompR P F a π w
  have hi := h2 σ hσ
  obtain ⟨h3, h4⟩ := satLoc P F a w σ
  obtain ⟨x, hx0, hx⟩ := h
  obtain ⟨B, hB⟩ := h3 (GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart (locGL F a w g) (f v)} => f.1) (fun f => f.2)
    (GlobalTheory.LFun.KGL w a : Set _) x hx0 hx (hi.2 ▸ Submodule.mem_top))
  exact ⟨B, (h4 _ _ hi B).2 hB⟩

end Proj

end HolRepCopy

section AutOf

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb GlobalTheory.CuspRep
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem aut_of (φ : TR.Sm F a) (h : IsAutomorphicForm φ.1) : TR.IsAutForm φ := by
  refine ⟨h.isLeftInvariant, ?_, ?_, (zfin_iff φ).2 h.isZFinite, fun g => ?_⟩
  · obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant h.isSmooth h.isKFinite
    refine isOpen_iff_mem_nhds.2 fun k hk => ?_
    have h1 : (fun x => k⁻¹ * x) ⁻¹' (U : Set _) ∈ nhds k :=
      (U.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using U.one_mem)
    filter_upwards [h1] with x hx
    refine Subtype.ext (funext fun g => ?_)
    have h2 := hU (g * finGL F a k) _ hx
    rw [finEmb_eq, mul_assoc, ← map_mul, mul_inv_cancel_left] at h2
    exact h2.trans (congrFun (congrArg Subtype.val hk) g)
  · have hk : FiniteDimensional ℂ _ := h.isKFinite
    refine FiniteDimensional.of_injective ((TR.Sm F a).subtype.restrict (q := Submodule.span ℂ (Set.range
      fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL F a)) => rightTranslate (k : AdelicGLn.AdelicGL F a) φ.1)) ?_) ?_
    · intro x hx
      refine Submodule.mem_comap.1 (Submodule.span_le.2 ?_ hx)
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨⟨TR.infGL F a (Unitary.toUnits k), ?_⟩, rfl⟩
      rw [← infEmb_grpEq]
      exact (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces F a _).2 k.2
    · intro x y hxy
      have h2 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h2)
  · obtain ⟨C, N, hC⟩ := h.hasModerateGrowth
    obtain ⟨M, hM⟩ := UpperTheory.adelicHeight_infGL_le_opNorm F a
    refine ⟨|C| * (heightConst F a * height g) ^ N, M * N, fun y => (hC _).trans ?_⟩
    have h0 : 0 ≤ heightConst F a * height g := mul_nonneg (zero_le_one.trans one_le_heightConst) (height_pos g).le
    rw [mul_assoc, pow_mul, ← mul_pow]
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le
      ((height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hM y) h0)) N) (pow_nonneg (height_pos _).le N) (abs_nonneg C)

end AutOf

section Form

open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

theorem zfin_of {φ : TR.Sm ℚ 3} (c : InfinitePlace ℚ → ℂ → ℂ) (h : ∀ v u, TR.cap v u φ = c v u • φ) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm ℚ 3) => z φ) '' TR.Zalg ℚ 3)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  change z φ ∈ Submodule.span ℂ {φ}
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, u, rfl⟩ := hx
    rw [h v u]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self φ)
  | algebraMap c' =>
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self φ)
  | add x y _ _ hx hy =>
    rw [LinearMap.add_apply]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hy
    rw [Module.End.mul_apply, ← hd, map_smul]
    exact Submodule.smul_mem _ _ hx

variable {V : Submodule ℂ (Ad3.G3 → ℂ)} (hV : Ad3.WhA V)

theorem isAut (U : V →ₗ[ℂ] archSmooth ℚ 3)
    (hU1 : ∀ W : V, IsLeftInvariant (U W : Ad3.G3 → ℂ) ∧ HasModerateGrowth (U W : Ad3.G3 → ℂ) ∧
      IsCuspidal (U W : Ad3.G3 → ℂ) ∧ FourierWhittaker.whittaker (U W : Ad3.G3 → ℂ) = W)
    (hU2 : ∀ (W : V) h g, (U ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩ : Ad3.G3 → ℂ) g = (U W : Ad3.G3 → ℂ) (g * h))
    (W : V) (hK : IsKFinite W.1) (hZ : IsZFinite (U W)) : IsAutomorphicForm (U W : Ad3.G3 → ℂ) where
  isLeftInvariant := (hU1 W).1
  isSmooth := ⟨(U W).2, fun g => by
    obtain ⟨O, hO⟩ := hV.level W.1 W.2
    filter_upwards [O.isOpen.mem_nhds O.one_mem] with y hy
    have e : (⟨fun x => W.1 (x * finEmb ℚ 3 y), hV.stable _ W.2 _⟩ : V) = W := Subtype.ext (funext fun x => hO x y hy)
    rw [← hU2 W (finEmb ℚ 3 y) g, e]⟩
  isKFinite := by
    unfold IsKFinite at hK ⊢
    set Sp := Submodule.span ℂ (Set.range fun k : (Reduction.maxCompact : Subgroup Ad3.G3) =>
      rightTranslate (k : Ad3.G3) W.1)
    have hle : Sp ≤ V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hV.stable _ W.2 _)
    let L : Sp →ₗ[ℂ] (Ad3.G3 → ℂ) := (archSmooth ℚ 3).subtype ∘ₗ U ∘ₗ Submodule.inclusion hle
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨⟨rightTranslate (k : Ad3.G3) W.1, Submodule.subset_span ⟨k, rfl⟩⟩, ?_⟩
    funext g
    exact hU2 W k g
  isZFinite := hZ
  hasModerateGrowth := (hU1 W).2.1

theorem inf_char (π₀ : TR.CuspSub ℚ 3) {φ ψ : TR.Sm ℚ 3} (hψ : ψ ∈ π₀.V) (h0 : ψ ≠ 0)
    (hz : ∀ z : Module.End ℂ (TR.Sm ℚ 3), (∀ V, TR.IsStable V → ∀ x ∈ V, z x ∈ V) → ∀ c : ℂ, z φ = c • φ → z ψ = c • ψ)
    (k : ℕ) (hcap : ∀ v u, TR.cap v u φ = ((u + (k - 1)) * u * (u - (k - 1))) • φ) (v : InfinitePlace ℚ) :
    π₀.HasInfChar v {(k : ℂ) - 1, 0, 1 - (k : ℂ)} :=
  ⟨rfl, fun u => cap_all π₀ hψ h0 v u _ (by
    rw [hz _ (fun V hV => TR.Zalg_stable (fun X => hV (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩)) _ (hcap v u)]
    congr 1
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton]
    ring)⟩

end Form

section Sat

open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GlobalTheory.CuspRep (locGL finGL)

abbrev uz (w : Ad3.Pl) : Ad3.Qv w := (GLnLocal.uniformizer (Ad3.Qv w) : Ad3.Qv w)

theorem isUnif (w : Ad3.Pl) : Formalism.UG.IsUnifV ℚ w (uz w) := (UpperTheory.V.Af.Smo.sphDict ℚ 3 w).2.1

theorem tj_finite (w : Ad3.Pl) (j : ℕ) :
    {c : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3 | Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out ≠ 0}.Finite :=
  Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm ℚ w 3) (GlobalTheory.LFun.Tj_mem_hecke (isUnif w) j).2

theorem finsum_tj {M : Type*} [AddCommMonoid M] [Module ℂ M] (w : Ad3.Pl) (j : ℕ)
    (f : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3 → M) :
    ∑ᶠ c, Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out • f c =
      ∑ c ∈ (tj_finite w j).toFinset, Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out • f c := by
  refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
  rw [Set.Finite.coe_toFinset]
  intro h0
  apply hc
  simp only [h0, zero_smul]

theorem finsum_tj_mul (w : Ad3.Pl) (j : ℕ) (f : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3 → ℂ) :
    ∑ᶠ c, Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out * f c =
      ∑ c ∈ (tj_finite w j).toFinset, Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out * f c := by
  simpa only [smul_eq_mul] using finsum_tj w j f

theorem sat_at (PH : UpperTheory.V.Af.HypothesesH) (π₀ : TR.CuspSub ℚ 3) {φ ψ : TR.Sm ℚ 3} (hψ : ψ ∈ π₀.V) (h0 : ψ ≠ 0)
    (hz : ∀ z : Module.End ℂ (TR.Sm ℚ 3), (∀ V, TR.IsStable V → ∀ x ∈ V, z x ∈ V) → ∀ c : ℂ, z φ = c • φ → z ψ = c • ψ)
    (w : Ad3.Pl) (B : Multiset ℂˣ) (hB : B.card = 3)
    (hinv : ∀ k ∈ GlobalTheory.LFun.KGL w 3, ∀ g, φ.1 (g * finGL ℚ 3 (locGL ℚ 3 w k)) = φ.1 g)
    (heig : ∀ j ≤ 3, ∀ g, ∑ᶠ c : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3,
      Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out * φ.1 (g * finGL ℚ 3 (locGL ℚ 3 w c.out)) =
        GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 B j * φ.1 g) :
    π₀.HasSat w B := by
  set x : π₀.V := ⟨ψ, hψ⟩
  have hx0 : x ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hfix : ∀ k ∈ GlobalTheory.LFun.KGL w 3, π₀.locRep w k x = x := fun k hk => Subtype.ext (by
    have h1 : TR.act (.fin (locGL ℚ 3 w k)) φ = (1 : ℂ) • φ :=
      (Subtype.ext (funext fun g => hinv k hk g)).trans (one_smul _ _).symm
    have := hz _ (fun V hV => hV (.fin _)) 1 h1
    rw [one_smul] at this
    exact this)
  obtain ⟨B', hB'⟩ := exists_sat PH.toClassicalTheorems π₀ w ⟨x, hx0, hfix⟩
  have hs := hB'.2 x (GlobalTheory.LGrp.mem_fixed.2 hfix) hx0
  have key : ∀ j ≤ 3, GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 B' j = GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 B j := by
    intro j hj
    set T := (tj_finite w j).toFinset
    set t : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3 → ℂ := fun c => Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out
    set z : Module.End ℂ (TR.Sm ℚ 3) := ∑ c ∈ T, t c • TR.act (.fin (locGL ℚ 3 w c.out))
    have hzφ : z φ = GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 B j • φ := by
      refine Subtype.ext (funext fun g => ?_)
      have h1 := heig j hj g
      rw [finsum_tj_mul w j (fun c => φ.1 (g * finGL ℚ 3 (locGL ℚ 3 w c.out)))] at h1
      change (z φ).1 g = (GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 B j • φ).1 g
      rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← h1]
      simp only [z, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun c _ => rfl
    have hzst : ∀ V, TR.IsStable V → ∀ y ∈ V, z y ∈ V := fun V hV y hy => by
      simp only [z, LinearMap.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hV (.fin _) y hy)
    have hzψ := hz z hzst _ hzφ
    have h2 := hs.2.2.2 (uz w) (isUnif w) j hj
    have h3 : GlobalTheory.LFun.heckeVec (π₀.locRep w) (GlobalTheory.LFun.KGL w 3) (Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j) x =
        ∑ c ∈ T, t c • π₀.locRep w c.out x := finsum_tj w j (fun c => π₀.locRep w c.out x)
    have h4 : ((∑ c ∈ T, t c • π₀.locRep w c.out x : π₀.V) : TR.Sm ℚ 3) = z ψ := by
      simp only [z, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
      rfl
    rw [h3] at h2
    have h5 := congrArg Subtype.val h2
    rw [h4, hzψ, Submodule.coe_smul] at h5
    exact (smul_left_injective ℂ h0 h5).symm
  have hBB : B' = B := GlobalTheory.LFun.eq_of_satEig_eq (GlobalTheory.LFun.qV_ne_zero w) hs.2.2.1 hB key
  rw [← hBB]
  exact hB'

variable {V : Submodule ℂ (Ad3.G3 → ℂ)} (hV : Ad3.WhA V)

theorem phi_loc (D : Ad3.Dat) (w : Ad3.Pl) (hg : UpperTheory.V.Af.Smo.GoodAt w (UpperTheory.V.Af.Smo.psiL w))
    (U : V →ₗ[ℂ] archSmooth ℚ 3)
    (hU2 : ∀ (W : V) h g, (U ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩ : Ad3.G3 → ℂ) g = (U W : Ad3.G3 → ℂ) (g * h))
    (W : V) (hs : Ad3.SphAt D w W.1) :
    (∀ k ∈ GlobalTheory.LFun.KGL w 3, ∀ g, (U W : Ad3.G3 → ℂ) (g * finGL ℚ 3 (locGL ℚ 3 w k)) = (U W : Ad3.G3 → ℂ) g) ∧
    ∀ j ≤ 3, ∀ g, ∑ᶠ c : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3,
      Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out * (U W : Ad3.G3 → ℂ) (g * finGL ℚ 3 (locGL ℚ 3 w c.out)) =
        GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 {D.ν w (unifUnit (Ad3.Qv w)), 1, (D.ν w (unifUnit (Ad3.Qv w)))⁻¹} j *
          (U W : Ad3.G3 → ℂ) g := by
  set fg : GL (Fin 3) (Ad3.Qv w) → Ad3.G3 := fun y => finGL ℚ 3 (locGL ℚ 3 w y)
  set rt : Ad3.G3 → V → V := fun h W => ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩

  have hWinv : ∀ k ∈ GlobalTheory.LFun.KGL w 3, ∀ g, W.1 (g * fg k) = W.1 g := fun k hk g => by
    obtain ⟨g1, x1, h⟩ := sph_transl D w W.1 hs g
    have e1 := h k
    have e2 := h 1
    simp only [fg, map_one, mul_one] at e2
    simp only [fg] at e1 ⊢
    rw [e1, e2, sph_inv w hg _ x1 hk]
  have hWeig : ∀ j ≤ 3, ∀ g, ∑ᶠ c : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3,
      Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out * W.1 (g * fg c.out) =
        GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 {D.ν w (unifUnit (Ad3.Qv w)), 1, (D.ν w (unifUnit (Ad3.Qv w)))⁻¹} j *
          W.1 g := fun j hj g => by
    obtain ⟨g1, x1, h⟩ := sph_transl D w W.1 hs g
    have e2 := h 1
    simp only [map_one, mul_one] at e2
    simp only [fg, h]
    rw [e2]
    have e3 := sph_eig w hg (D.ν w) j hj x1
    rw [finsum_tj_mul w j] at e3 ⊢
    rw [show ∀ a b c : ℂ, a * (b * c) = b * (a * c) from fun a b c => by ring, ← e3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  refine ⟨fun k hk g => ?_, fun j hj g => ?_⟩
  · have e : rt (fg k) W = W := Subtype.ext (funext fun x => hWinv k hk x)
    rw [← hU2 W (fg k) g]
    exact congrArg (fun W' : V => (U W' : Ad3.G3 → ℂ) g) e
  · set T := (tj_finite w j).toFinset
    set t : GL (Fin 3) (Ad3.Qv w) ⧸ GlobalTheory.LFun.KGL w 3 → ℂ := fun c => Formalism.UG.Tj ℂ 3 (Formalism.UG.Ov ℚ w) (uz w) j c.out
    have hsum : ∑ c ∈ T, t c • rt (fg c.out) W =
        GlobalTheory.LFun.satEig (Formalism.UG.qV ℚ w) 3 {D.ν w (unifUnit (Ad3.Qv w)), 1, (D.ν w (unifUnit (Ad3.Qv w)))⁻¹} j • W := by
      refine Subtype.ext (funext fun x => ?_)
      have h1 := hWeig j hj x
      rw [finsum_tj_mul w j (fun c => W.1 (x * fg c.out))] at h1
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact h1
    have h2 := congrArg (fun W' : V => (U W' : Ad3.G3 → ℂ) g) hsum
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h2
    rw [finsum_tj_mul w j (fun c => (U W : Ad3.G3 → ℂ) (g * fg c.out)), ← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hU2]

end Sat

open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
theorem main (PH : UpperTheory.V.Af.HypothesesH) (D : Ad3.Dat) (V : Submodule ℂ (Ad3.G3 → ℂ)) (hV : Ad3.WhA V)
    (hG : Ad3.Good D V hV) (U : V →ₗ[ℂ] archSmooth ℚ 3)
    (hU1 : ∀ W : V, IsLeftInvariant (U W : Ad3.G3 → ℂ) ∧ HasModerateGrowth (U W : Ad3.G3 → ℂ) ∧
      IsCuspidal (U W : Ad3.G3 → ℂ) ∧ FourierWhittaker.whittaker (U W : Ad3.G3 → ℂ) = W)
    (hU2 : ∀ (W : V) h g, (U ⟨fun x => W.1 (x * h), hV.stable _ W.2 h⟩ : Ad3.G3 → ℂ) g = (U W : Ad3.G3 → ℂ) (g * h))
    (hU3 : ∀ (W : V) i j, U ⟨_, hV.lie _ W.2 i j⟩ = Ad3.EA i j (U W)) :
    ∃ P : TR.CuspSub ℚ 3, (∀ v, P.HasInfChar v {(D.k : ℂ) - 1, 0, 1 - (D.k : ℂ)}) ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
        P.HasSat w {D.ν w (unifUnit (Ad3.Qv w)), 1, (D.ν w (unifUnit (Ad3.Qv w)))⁻¹} := by
  obtain ⟨-, hcap, htr, W0, hW0V, hW0, hKf, S, hsph⟩ := hG
  set W : V := ⟨W0, hW0V⟩
  set φ : TR.Sm ℚ 3 := (Fb.smEq ℚ 3).symm (U W) with hφ
  have hcapφ := cap_form hV D.k hcap U hU3 W
  have hZ : IsZFinite (U W) := by
    have h := (Fb.zfin_iff φ).1 (zfin_of _ hcapφ)
    rwa [hφ, LinearEquiv.apply_symm_apply] at h
  have hA := isAut hV U hU1 hU2 W hKf hZ
  have hcusp : TR.IsCuspForm φ := ⟨aut_of φ hA, UpperTheory.isCuspidal_of_constantTerm_eq_zero ℚ 3 _ hA.isLeftInvariant hA.continuous (hU1 W).2.2.1⟩
  have hφ0 : φ ≠ 0 := by
    intro h
    apply hW0
    have h1 : (U W : Ad3.G3 → ℂ) = 0 := congrArg Subtype.val h
    have h2 := (hU1 W).2.2.2
    rw [h1] at h2
    have h3 : W0 = FourierWhittaker.whittaker 0 := h2.symm
    rw [h3]
    funext g
    simp [FourierWhittaker.whittaker]
  obtain ⟨π₀, ψ, hψ, h0, hz⟩ := proj hφ0 (UpperTheory.V.Af.cuspSemisimpleReal_dB ℚ 3 φ hcusp
    ⟨0, by rw [trace_form hV htr U hU3 W, zero_smul]⟩)
  refine ⟨π₀, fun v => inf_char π₀ hψ h0 hz D.k hcapφ v, ?_⟩
  have hcof : ∀ᶠ w : Ad3.Pl in Filter.cofinite, w ∉ S ∧ UpperTheory.V.Af.Smo.GoodAt w (UpperTheory.V.Af.Smo.psiL w) :=
    (S.finite_toSet.eventually_cofinite_notMem).and (UpperTheory.V.Af.Smo.psiLoc ℚ).2
  filter_upwards [hcof] with w hw
  obtain ⟨hinv, heig⟩ := phi_loc hV D w hw.2 U hU2 W (hsph w hw.1)
  exact sat_at PH π₀ hψ h0 hz w _ rfl hinv heig

end Ad3P.CuspidalityAtInfinity
