import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicTensorAcyclicFlatEtaleComplexStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.TensQis
variable {R : Type} [CommRing R]
theorem sm_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl
theorem sm_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl
theorem sm_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map (-φ) x = -Sec.map φ x := rfl
theorem sm_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl
theorem sm_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl
theorem sm_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun k => k.hom x) (φ.hom.naturality g.op)
theorem sm_madd {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) : Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem sm_mzero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sm_munits {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (e : ℤˣ) (x : Sec F U) : Sec.map φ (e • x) = e • Sec.map φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _
theorem rs_madd {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ _ _

section Cone
variable {K L : Cx R} (φ : K ⟶ L) {U : Scheme.{0}}

theorem fst_inl (p : ℤ) (a : Sec (K.X (p + 1)) U) :
    Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) (Sec.map ((mappingCone.inl φ).v (p + 1) p (by omega)) a) = a := by
  rw [← sm_comp, mappingCone.inl_v_fst_v φ (p + 1) p rfl, sm_id]
theorem fst_inr (p : ℤ) (a : Sec (L.X p) U) :
    Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) (Sec.map ((mappingCone.inr φ).f p) a) = 0 := by
  rw [← sm_comp, mappingCone.inr_f_fst_v φ p (p + 1) rfl, sm_zero]
theorem snd_inl (p : ℤ) (a : Sec (K.X (p + 1)) U) :
    Sec.map ((mappingCone.snd φ).v p p (add_zero p)) (Sec.map ((mappingCone.inl φ).v (p + 1) p (by omega)) a) = 0 := by
  rw [← sm_comp, mappingCone.inl_v_snd_v φ (p + 1) p (by omega), sm_zero]
theorem snd_inr (p : ℤ) (a : Sec (L.X p) U) :
    Sec.map ((mappingCone.snd φ).v p p (add_zero p)) (Sec.map ((mappingCone.inr φ).f p) a) = a := by
  rw [← sm_comp, mappingCone.inr_f_snd_v φ p, sm_id]
theorem cone_eta (p : ℤ) (z : Sec ((mappingCone φ).X p) U) :
    z = Sec.map ((mappingCone.inl φ).v (p + 1) p (by omega)) (Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z) +
      Sec.map ((mappingCone.inr φ).f p) (Sec.map ((mappingCone.snd φ).v p p (add_zero p)) z) := by
  have := congrArg (fun k => Sec.map k z) (mappingCone.id_X φ p (p + 1) rfl)
  beta_reduce at this
  rw [sm_add, sm_comp, sm_comp, sm_id] at this
  exact this.symm
theorem cone_ext {p : ℤ} {z z' : Sec ((mappingCone φ).X p) U}
    (h1 : Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z = Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z')
    (h2 : Sec.map ((mappingCone.snd φ).v p p (add_zero p)) z = Sec.map ((mappingCone.snd φ).v p p (add_zero p)) z') : z = z' := by
  rw [cone_eta φ p z, cone_eta φ p z', h1, h2]
theorem fst_d (p : ℤ) (z : Sec ((mappingCone φ).X p) U) :
    Sec.map ((mappingCone.fst φ).1.v (p + 1) (p + 1 + 1) rfl) (Sec.map ((mappingCone φ).d p (p + 1)) z) =
      -Sec.map (K.d (p + 1) (p + 1 + 1)) (Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z) := by
  rw [← sm_comp, mappingCone.d_fst_v φ p (p + 1) (p + 1 + 1) rfl rfl, sm_neg, sm_comp]
theorem snd_d (p : ℤ) (z : Sec ((mappingCone φ).X p) U) :
    Sec.map ((mappingCone.snd φ).v (p + 1) (p + 1) (add_zero _)) (Sec.map ((mappingCone φ).d p (p + 1)) z) =
      Sec.map (φ.f (p + 1)) (Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z) +
        Sec.map (L.d p (p + 1)) (Sec.map ((mappingCone.snd φ).v p p (add_zero p)) z) := by
  rw [← sm_comp, mappingCone.d_snd_v φ p (p + 1) rfl, sm_add, sm_comp, sm_comp]
end Cone

variable {I I' J T T' : Cx R}

def coneMul (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec ((mappingCone f).X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec ((mappingCone u).X w) U :=
  ((τ.mul U (s + 1) t (w + 1) (by omega)) ∘ₗ (((mappingCone.fst f).1.v s (s + 1) rfl).hom.app (op U)).hom).compr₂
      (((mappingCone.inl u).v (w + 1) w (by omega)).hom.app (op U)).hom +
    ((τ'.mul U s t w h) ∘ₗ (((mappingCone.snd f).v s s (add_zero s)).hom.app (op U)).hom).compr₂
      (((mappingCone.inr u).f w).hom.app (op U)).hom

theorem coneMul_apply (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (c : Sec ((mappingCone f).X s) U) (b : Sec (J.X t) U) :
    coneMul τ τ' f u U s t w h c b =
      Sec.map ((mappingCone.inl u).v (w + 1) w (by omega))
          (τ.mul U (s + 1) t (w + 1) (by omega) (Sec.map ((mappingCone.fst f).1.v s (s + 1) rfl) c) b) +
        Sec.map ((mappingCone.inr u).f w) (τ'.mul U s t w h (Sec.map ((mappingCone.snd f).v s s (add_zero s)) c) b) := rfl

def conePair (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (hc : τ.Compat τ' f (𝟙 J) u) :
    Pair (mappingCone f) J (mappingCone u) where
  mul := coneMul τ τ' f u
  nat := by
    intro V U g s t w h c b
    rw [coneMul_apply, coneMul_apply, rs_madd, ← sm_res, ← sm_res, τ.nat, τ'.nat, ← sm_res, ← sm_res]
  leibniz := by
    intro U s t w h c b
    apply cone_ext u
    · rw [← sm_comp, mappingCone.d_fst_v u w (w + 1) (w + 1 + 1) rfl rfl, sm_neg, sm_comp]
      simp only [coneMul_apply, sm_madd, sm_munits, fst_inl, fst_inr, add_zero, fst_d, map_neg, LinearMap.neg_apply, τ.leibniz]
      rw [Int.negOnePow_succ, Units.neg_smul, neg_add, neg_neg]
    · rw [← sm_comp, mappingCone.d_snd_v u w (w + 1) rfl, sm_add, sm_comp, sm_comp]
      simp only [coneMul_apply, sm_madd, sm_munits, snd_inl, snd_inr, fst_inl, fst_inr, zero_add, add_zero, snd_d,
        LinearMap.map_add₂, τ'.leibniz, hc, HomologicalComplex.id_f, sm_id]
      rw [hc U (s + 1) t (w + 1) (by omega), HomologicalComplex.id_f, sm_id]
      abel

end GlobalTheory.EtC.TensQis
end

noncomputable section
namespace GlobalTheory.EtC.TensQis
open scoped DirectSum TensorProduct
variable {R : Type} [CommRing R] {I I' J T T' : Cx R}

def upI (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w + 1} :=
  ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩

def dnI (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w + 1}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.1 - 1, p.1.2), by have := p.2; omega⟩

def tInl (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) : Tens I J U (w + 1) →ₗ[ULift.{1} R] Tens (mappingCone f) J U w :=
  by classical exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof _ _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) (dnI w p) ∘ₗ
      TensorProduct.map (((mappingCone.inl f).v p.1.1 (p.1.1 - 1) (by omega)).hom.app (op U)).hom LinearMap.id

def tInr (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) : Tens I' J U w →ₗ[ULift.{1} R] Tens (mappingCone f) J U w :=
  by classical exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof _ _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p ∘ₗ
      TensorProduct.map (((mappingCone.inr f).f p.1.1).hom.app (op U)).hom LinearMap.id

def tFst (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) : Tens (mappingCone f) J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  by classical exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof _ _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w + 1} =>
        Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) (upI w p) ∘ₗ
      TensorProduct.map (((mappingCone.fst f).1.v p.1.1 (p.1.1 + 1) rfl).hom.app (op U)).hom LinearMap.id

def tSnd (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) : Tens (mappingCone f) J U w →ₗ[ULift.{1} R] Tens I' J U w :=
  by classical exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof _ _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        Sec (I'.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p ∘ₗ
      TensorProduct.map (((mappingCone.snd f).v p.1.1 p.1.1 (add_zero _)).hom.app (op U)).hom LinearMap.id

theorem mul_fst_inl (f : I ⟶ I') (τ : Pair I J T) (U : Scheme.{0}) (s t w' : ℤ) (hst : s + t = w') (s' : ℤ) (e : s' = s)
    (h1 : s' + t = w') (h2 : s - 1 + 1 = s') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    τ.mul U s' t w' h1 (Sec.map ((mappingCone.fst f).1.v (s - 1) s' h2) (Sec.map ((mappingCone.inl f).v s (s - 1) (by omega)) a)) b =
      τ.mul U s t w' hst a b := by
  subst e
  rw [← sm_comp, mappingCone.inl_v_fst_v, sm_id]

theorem lift_tInl (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (hc : τ.Compat τ' f (𝟙 J) u)
    (U : Scheme.{0}) (w : ℤ) (x : Tens I J U (w + 1)) :
    (conePair τ τ' f u hc).lift U w (tInl f U w x) = Sec.map ((mappingCone.inl u).v (w + 1) w (by omega)) (τ.lift U (w + 1) x) := by
  have : (conePair τ τ' f u hc).lift U w ∘ₗ tInl f U w =
      (((mappingCone.inl u).v (w + 1) w (by omega)).hom.app (op U)).hom ∘ₗ τ.lift U (w + 1) := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.comp_apply, tInl, Pair.lift, DirectSum.toModule_lof, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.lift.tmul]
    change coneMul τ τ' f u U (s - 1) t w (by omega) (Sec.map ((mappingCone.inl f).v s (s - 1) (by omega)) a) b =
      Sec.map ((mappingCone.inl u).v (w + 1) w (by omega)) (τ.mul U s t (w + 1) hp a b)
    rw [coneMul_apply, ← sm_comp _ ((mappingCone.snd f).v _ _ _), mappingCone.inl_v_snd_v, sm_zero, map_zero,
      LinearMap.zero_apply, sm_mzero, add_zero, mul_fst_inl f τ U s t (w + 1) hp _ (by omega)]
  exact congrArg (fun k => k x) this

theorem lift_tInr (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (hc : τ.Compat τ' f (𝟙 J) u)
    (U : Scheme.{0}) (w : ℤ) (x : Tens I' J U w) :
    (conePair τ τ' f u hc).lift U w (tInr f U w x) = Sec.map ((mappingCone.inr u).f w) (τ'.lift U w x) := by
  have : (conePair τ τ' f u hc).lift U w ∘ₗ tInr f U w = (((mappingCone.inr u).f w).hom.app (op U)).hom ∘ₗ τ'.lift U w := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.comp_apply, tInr, Pair.lift, DirectSum.toModule_lof, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.lift.tmul]
    change coneMul τ τ' f u U s t w hp (Sec.map ((mappingCone.inr f).f s) a) b =
      Sec.map ((mappingCone.inr u).f w) (τ'.mul U s t w hp a b)
    rw [coneMul_apply, fst_inr, map_zero, LinearMap.zero_apply, sm_mzero, zero_add, snd_inr]
  exact congrArg (fun k => k x) this

theorem lof_shift (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) [DecidableEq {p : ℤ × ℤ // p.1 + p.2 = w}] (s t : ℤ) (hp : s + t = w)
    (s'' : ℤ) (e : s'' = s) (h : s'' + t = w) (h' : s + 1 + -1 = s'') (y : Sec (I.X (s + 1)) U) (b : Sec (J.X t) U) :
    DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s'', t), h⟩
        (Sec.map ((mappingCone.inl f).v (s + 1) s'' h') y ⊗ₜ b) =
      DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s, t), hp⟩
        (Sec.map ((mappingCone.inl f).v (s + 1) s (by omega)) y ⊗ₜ b) := by
  subst e; rfl

theorem tDecomp (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) (x : Tens (mappingCone f) J U w) :
    tInl f U w (tFst f U w x) + tInr f U w (tSnd f U w x) = x := by
  have : (tInl f U w ∘ₗ tFst f U w + tInr f U w ∘ₗ tSnd f U w :
      Tens (mappingCone f) J U w →ₗ[ULift.{1} R] Tens (mappingCone f) J U w) = LinearMap.id := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.add_apply, LinearMap.comp_apply, tInl, tInr, tFst, tSnd, DirectSum.toModule_lof,
      TensorProduct.map_tmul, LinearMap.id_apply]
    change DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s + 1 - 1, t), by omega⟩
        (Sec.map ((mappingCone.inl f).v (s + 1) (s + 1 - 1) (by omega)) (Sec.map ((mappingCone.fst f).1.v s (s + 1) rfl) a) ⊗ₜ b) +
      DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s, t), hp⟩
        (Sec.map ((mappingCone.inr f).f s) (Sec.map ((mappingCone.snd f).v s s (add_zero s)) a) ⊗ₜ b) =
      DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s, t), hp⟩ (a ⊗ₜ b)
    rw [lof_shift f U w s t hp _ (by omega), ← map_add, ← TensorProduct.add_tmul, ← cone_eta]
  exact congrArg (fun k => k x) this

theorem res_tInl (f : I ⟶ I') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U (w + 1)) :
    Tens.res g w (tInl f U w x) = tInl f V w (Tens.res g (w + 1) x) := by
  have : (Tens.res g w ∘ₗ tInl f U w : Tens I J U (w + 1) →ₗ[ULift.{1} R] Tens (mappingCone f) J V w) =
      tInl f V w ∘ₗ Tens.res g (w + 1) := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.comp_apply, tInl, Tens.res, DirectSum.toModule_lof, DirectSum.lmap_lof, TensorProduct.map_tmul,
      LinearMap.id_apply]
    congr 1
    change Sec.res g (Sec.map ((mappingCone.inl f).v s (s - 1) (by omega)) a) ⊗ₜ[ULift.{1} R] Sec.res g b =
      Sec.map ((mappingCone.inl f).v s (s - 1) (by omega)) (Sec.res g a) ⊗ₜ[ULift.{1} R] Sec.res g b
    rw [sm_res]
  exact congrArg (fun k => k x) this

theorem res_tInr (f : I ⟶ I') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I' J U w) :
    Tens.res g w (tInr f U w x) = tInr f V w (Tens.res g w x) := by
  have : (Tens.res g w ∘ₗ tInr f U w : Tens I' J U w →ₗ[ULift.{1} R] Tens (mappingCone f) J V w) =
      tInr f V w ∘ₗ Tens.res g w := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.comp_apply, tInr, Tens.res, DirectSum.toModule_lof, DirectSum.lmap_lof, TensorProduct.map_tmul,
      LinearMap.id_apply]
    congr 1
    change Sec.res g (Sec.map ((mappingCone.inr f).f s) a) ⊗ₜ[ULift.{1} R] Sec.res g b =
      Sec.map ((mappingCone.inr f).f s) (Sec.res g a) ⊗ₜ[ULift.{1} R] Sec.res g b
    rw [sm_res]
  exact congrArg (fun k => k x) this

theorem conePair_isTensor (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (hc : τ.Compat τ' f (𝟙 J) u)
    (hτ : τ.IsTensor) (hτ' : τ'.IsTensor) : (conePair τ τ' f u hc).IsTensor := by
  obtain ⟨-, loc_mono, loc_and, -, -, -, -⟩ := GlobalTheory.EtC.loc_calculus
  constructor
  · intro U w y
    have h1 := hτ.1 U (w + 1) (Sec.map ((mappingCone.fst u).1.v w (w + 1) rfl) y)
    have h2 := hτ'.1 U w (Sec.map ((mappingCone.snd u).v w w (add_zero w)) y)
    refine loc_mono _ _ _ (loc_and _ _ _ h1 h2) ?_
    rintro V g ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩
    refine ⟨tInl f V w x1 + tInr f V w x2, ?_⟩
    rw [map_add, lift_tInl, lift_tInr, hx1, hx2, sm_res, sm_res, ← rs_madd, ← cone_eta]
  · intro U w x hx
    rw [← tDecomp f U w x, map_add, lift_tInl, lift_tInr] at hx
    have e1 : τ.lift U (w + 1) (tFst f U w x) = 0 := by
      have := congrArg (fun z => Sec.map ((mappingCone.fst u).1.v w (w + 1) rfl) z) hx
      simpa only [sm_madd, fst_inl, fst_inr, add_zero, sm_mzero] using this
    have e2 : τ'.lift U w (tSnd f U w x) = 0 := by
      have := congrArg (fun z => Sec.map ((mappingCone.snd u).v w w (add_zero w)) z) hx
      simpa only [sm_madd, snd_inl, snd_inr, zero_add, sm_mzero] using this
    refine loc_mono _ _ _ (loc_and _ _ _ (hτ.2 U (w + 1) _ e1) (hτ'.2 U w _ e2)) ?_
    rintro V g ⟨h1, h2⟩
    rw [← tDecomp f U w x, map_add, res_tInl, res_tInr, h1, h2, map_zero, map_zero, add_zero]

theorem quasiIso_of_cone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

end GlobalTheory.EtC.TensQis

namespace GlobalTheory.EtC

theorem tensor_quasiIso : ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0]
    [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) →
    ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u := by
  intro R _ I I' J T T' _ _ _ τ τ' hτ hτ' hJ f _ u hc
  haveI : (mappingCone f).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone f 0 0 (-1)
  have hC := GlobalTheory.mappingCone_acyclic_of_quasiIso f
  exact TensQis.quasiIso_of_cone_acyclic u (GlobalTheory.T.acyclic_tensor_acyclic_flatEtaleComplex R (-1) 0 (TensQis.conePair τ τ' f u hc)
    (TensQis.conePair_isTensor τ τ' f u hc hτ hτ') hJ hC)

end GlobalTheory.EtC
end
