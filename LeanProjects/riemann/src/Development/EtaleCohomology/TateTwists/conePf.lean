import Development.EtaleCohomology.TateTwists.EtaleTensorPreservesQuasiIsoOfAcyclicAndCone

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.conePf

noncomputable section
open scoped TensorProduct DirectSum

variable {R : Type} [CommRing R]

theorem sm_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sm_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem sm_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-φ) x = -Sec.map φ x := rfl

theorem sm_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem sm_madd {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := (φ.hom.app (op U)).hom.map_add x y

theorem sm_msmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤˣ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := by
  rcases Int.units_eq_one_or c with rfl | rfl
  · simp
  · simp only [Units.neg_smul, one_smul]; exact (φ.hom.app (op U)).hom.map_neg x

theorem sm_mzero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  (φ.hom.app (op U)).hom.map_zero

theorem sm_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem sm_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  exact (congrArg (fun m => m.hom x) (φ.hom.naturality g.op)).symm

abbrev secL {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Sec F U →ₗ[ULift.{1} R] Sec G U := (φ.hom.app (op U)).hom

theorem cone_ext {I I' : Cx R} (f : I ⟶ I') {n : ℤ} {U : Scheme.{0}} (y z : Sec ((mappingCone f).X n) U)
    (h1 : Sec.map ((mappingCone.fst f).1.v n (n + 1) rfl) y = Sec.map ((mappingCone.fst f).1.v n (n + 1) rfl) z)
    (h2 : Sec.map ((mappingCone.snd f).v n n (add_zero n)) y = Sec.map ((mappingCone.snd f).v n n (add_zero n)) z) :
    y = z := by
  rw [← sm_id y, ← sm_id z, ← mappingCone.id_X f n (n + 1) rfl, sm_add, sm_add, sm_comp, sm_comp, sm_comp, sm_comp, h1, h2]

def σmul {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T')
    (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec ((mappingCone f).X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec ((mappingCone u).X w) U :=
  ((τ.mul U (s + 1) t (w + 1) (by omega)).comp (secL ((mappingCone.fst f).1.v s (s + 1) rfl) U)).compr₂
      (secL ((mappingCone.inl u).v (w + 1) w (by omega)) U) +
    ((τ'.mul U s t w h).comp (secL ((mappingCone.snd f).v s s (add_zero s)) U)).compr₂
      (secL ((mappingCone.inr u).f w) U)

theorem σmul_apply {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T')
    (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) x b :
    σmul τ τ' f u U s t w h x b =
      Sec.map ((mappingCone.inl u).v (w + 1) w (by omega))
          (τ.mul U (s + 1) t (w + 1) (by omega) (Sec.map ((mappingCone.fst f).1.v s (s + 1) rfl) x) b) +
        Sec.map ((mappingCone.inr u).f w) (τ'.mul U s t w h (Sec.map ((mappingCone.snd f).v s s (add_zero s)) x) b) := rfl

theorem σ_fst {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T')
    (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) x b :
    Sec.map ((mappingCone.fst u).1.v w (w + 1) rfl) (σmul τ τ' f u U s t w h x b) =
      τ.mul U (s + 1) t (w + 1) (by omega) (Sec.map ((mappingCone.fst f).1.v s (s + 1) rfl) x) b := by
  rw [σmul_apply, sm_madd, ← sm_comp, ← sm_comp, mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v, sm_id, sm_zero, add_zero]

theorem σ_snd {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T')
    (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) x b :
    Sec.map ((mappingCone.snd u).v w w (add_zero w)) (σmul τ τ' f u U s t w h x b) =
      τ'.mul U s t w h (Sec.map ((mappingCone.snd f).v s s (add_zero s)) x) b := by
  rw [σmul_apply, sm_madd, ← sm_comp, ← sm_comp, mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, sm_id, sm_zero, zero_add]

theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := (F.obj.map g.op).hom.map_add x y

theorem σ_nat {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T')
    {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) x b :
    Sec.res g (σmul τ τ' f u U s t w h x b) = σmul τ τ' f u V s t w h (Sec.res g x) (Sec.res g b) := by
  rw [σmul_apply, σmul_apply, res_add, sm_res, sm_res, τ.nat, τ'.nat, sm_res, sm_res]

theorem σ_leib {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T')
    (hc : τ.Compat τ' f (𝟙 J) u)
    (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) x b :
    Sec.map ((mappingCone u).d w (w + 1)) (σmul τ τ' f u U s t w h x b) =
      σmul τ τ' f u U (s + 1) t (w + 1) (by omega) (Sec.map ((mappingCone f).d s (s + 1)) x) b +
        s.negOnePow • σmul τ τ' f u U s (t + 1) (w + 1) (by omega) x (Sec.map (J.d t (t + 1)) b) := by
  apply cone_ext
  · rw [← sm_comp, mappingCone.d_fst_v u w (w + 1) (w + 1 + 1) rfl rfl, sm_neg, sm_comp, σ_fst, sm_madd, sm_msmul, σ_fst, σ_fst,
      ← sm_comp, mappingCone.d_fst_v f s (s + 1) (s + 1 + 1) rfl rfl, sm_neg, sm_comp, τ.leibniz]
    simp only [map_neg, LinearMap.neg_apply, Int.negOnePow_succ, Units.neg_smul]
    abel
  · rw [← sm_comp, mappingCone.d_snd_v u w (w + 1) rfl, sm_add, sm_comp, sm_comp, σ_fst, σ_snd, sm_madd, sm_msmul,
      σ_snd, σ_snd, ← sm_comp, mappingCone.d_snd_v f s (s + 1) rfl, sm_add, sm_comp, sm_comp, hc, τ'.leibniz]
    simp only [map_add, LinearMap.add_apply, HomologicalComplex.id_f, sm_id]
    abel

def σ {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T')
    (hc : τ.Compat τ' f (𝟙 J) u) : Pair (mappingCone f) J (mappingCone u) where
  mul := σmul τ τ' f u
  nat g s t w h x b := σ_nat τ τ' f u g s t w h x b
  leibniz U s t w h x b := σ_leib τ τ' f u hc U s t w h x b

section Tensor

variable {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T')

def P1 (U : Scheme.{0}) (w : ℤ) : Tens (mappingCone f) J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) := by
  classical
  exact DirectSum.toModule _ _ _ fun p => (DirectSum.lof _ _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
    Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩).comp
    (TensorProduct.map (secL ((mappingCone.fst f).1.v p.1.1 (p.1.1 + 1) rfl) U) LinearMap.id)

def P2 (U : Scheme.{0}) (w : ℤ) : Tens (mappingCone f) J U w →ₗ[ULift.{1} R] Tens I' J U w :=
  DirectSum.lmap fun p => TensorProduct.map (secL ((mappingCone.snd f).v p.1.1 p.1.1 (add_zero _)) U) LinearMap.id

def Q1 (U : Scheme.{0}) (w : ℤ) : Tens I J U (w + 1) →ₗ[ULift.{1} R] Tens (mappingCone f) J U w := by
  classical
  exact DirectSum.toModule _ _ _ fun q => (DirectSum.lof _ _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
    Sec ((mappingCone f).X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(q.1.1 - 1, q.1.2), by have := q.2; omega⟩).comp
    (TensorProduct.map (secL ((mappingCone.inl f).v q.1.1 (q.1.1 - 1) (by omega)) U) LinearMap.id)

def Q2 (U : Scheme.{0}) (w : ℤ) : Tens I' J U w →ₗ[ULift.{1} R] Tens (mappingCone f) J U w :=
  DirectSum.lmap fun p => TensorProduct.map (secL ((mappingCone.inr f).f p.1.1) U) LinearMap.id

theorem etale_mapping_cone_pairing_fst_comp_lift (hc : τ.Compat τ' f (𝟙 J) u) (U : Scheme.{0}) (w : ℤ) :
    (τ.lift U (w + 1)).comp (P1 f U w) = (secL ((mappingCone.fst u).1.v w (w + 1) rfl) U).comp ((σ τ τ' f u hc).lift U w) := by
  classical
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, P1, Pair.lift, DirectSum.toModule_lof, TensorProduct.map_tmul, TensorProduct.lift.tmul,
    LinearMap.id_apply]
  exact (σ_fst τ τ' f u U _ _ _ p.2 a b).symm

theorem etale_mapping_cone_pairing_snd_comp_lift (hc : τ.Compat τ' f (𝟙 J) u) (U : Scheme.{0}) (w : ℤ) :
    (τ'.lift U w).comp (P2 f U w) = (secL ((mappingCone.snd u).v w w (add_zero w)) U).comp ((σ τ τ' f u hc).lift U w) := by
  classical
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, P2, Pair.lift, DirectSum.toModule_lof, DirectSum.lmap_lof, TensorProduct.map_tmul,
    TensorProduct.lift.tmul, LinearMap.id_apply]
  exact (σ_snd τ τ' f u U _ _ _ p.2 a b).symm

theorem etale_mapping_cone_pairing_lift_comp_inr_incl (hc : τ.Compat τ' f (𝟙 J) u) (U : Scheme.{0}) (w : ℤ) :
    ((σ τ τ' f u hc).lift U w).comp (Q2 f U w) = (secL ((mappingCone.inr u).f w) U).comp (τ'.lift U w) := by
  classical
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, Q2, Pair.lift, DirectSum.toModule_lof, DirectSum.lmap_lof, TensorProduct.map_tmul,
    TensorProduct.lift.tmul, LinearMap.id_apply]
  show σmul τ τ' f u U _ _ _ p.2 _ b = _
  rw [σmul_apply, ← sm_comp, ← sm_comp, mappingCone.inr_f_fst_v, mappingCone.inr_f_snd_v, sm_id, sm_zero, map_zero,
    LinearMap.zero_apply, sm_mzero, zero_add]

theorem shiftA (U : Scheme.{0}) (q1 q2 w : ℤ) (hq : q1 + q2 = w + 1) (k : ℤ) (hk : k = q1) (h1 : k + q2 = w + 1)
    (h2 : q1 - 1 + 1 = k) (h3 : q1 + -1 = q1 - 1) (a : Sec (I.X q1) U) (b : Sec (J.X q2) U) :
    τ.mul U k q2 (w + 1) h1 (Sec.map ((mappingCone.fst f).1.v (q1 - 1) k h2) (Sec.map ((mappingCone.inl f).v q1 (q1 - 1) h3) a)) b =
      τ.mul U q1 q2 (w + 1) hq a b := by
  subst hk
  rw [← sm_comp, mappingCone.inl_v_fst_v, sm_id]

theorem etale_mapping_cone_pairing_lift_comp_inl_incl (hc : τ.Compat τ' f (𝟙 J) u) (U : Scheme.{0}) (w : ℤ) :
    ((σ τ τ' f u hc).lift U w).comp (Q1 f U w) =
      (secL ((mappingCone.inl u).v (w + 1) w (by omega)) U).comp (τ.lift U (w + 1)) := by
  classical
  refine DirectSum.linearMap_ext _ fun q => TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, Q1, Pair.lift, DirectSum.toModule_lof, TensorProduct.map_tmul,
    TensorProduct.lift.tmul, LinearMap.id_apply]
  show σmul τ τ' f u U (q.1.1 - 1) q.1.2 w (by have := q.2; omega)
      (Sec.map ((mappingCone.inl f).v q.1.1 (q.1.1 - 1) (by omega)) a) b =
    Sec.map ((mappingCone.inl u).v (w + 1) w (by omega)) (τ.mul U q.1.1 q.1.2 (w + 1) q.2 a b)
  rw [σmul_apply, shiftA τ f U q.1.1 q.1.2 w q.2 _ (by omega),
    ← sm_comp ((mappingCone.inl f).v _ _ _) ((mappingCone.snd f).v _ _ _), mappingCone.inl_v_snd_v, sm_zero, map_zero,
    LinearMap.zero_apply, sm_mzero, add_zero]

theorem etale_mapping_cone_tensor_fst_proj_res_comm {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens (mappingCone f) J U w) :
    Tens.res g (w + 1) (P1 f U w x) = P1 f V w (Tens.res g w x) := by
  classical
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply (P1 f V w)]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, P1, Tens.res, DirectSum.toModule_lof, DirectSum.lmap_lof, TensorProduct.map_tmul,
    LinearMap.id_apply]
  congr 2
  exact sm_res _ g a

theorem etale_mapping_cone_tensor_snd_proj_res_comm {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens (mappingCone f) J U w) :
    Tens.res g w (P2 f U w x) = P2 f V w (Tens.res g w x) := by
  classical
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply (P2 f V w)]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, P2, Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, LinearMap.id_apply]
  congr 2
  exact sm_res _ g a

theorem shiftB (U : Scheme.{0}) (p1 p2 w : ℤ) (hp : p1 + p2 = w) (k : ℤ) (hk : k = p1) (h1 : k + p2 = w)
    (h3 : p1 + 1 + -1 = k) (a : Sec ((mappingCone f).X p1) U) (b : Sec (J.X p2) U) :
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec ((mappingCone f).X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(k, p2), h1⟩
      (Sec.map ((mappingCone.inl f).v (p1 + 1) k h3) (Sec.map ((mappingCone.fst f).1.v p1 (p1 + 1) rfl) a) ⊗ₜ b) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec ((mappingCone f).X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(p1, p2), hp⟩
      (Sec.map ((mappingCone.fst f).1.v p1 (p1 + 1) rfl ≫ (mappingCone.inl f).v (p1 + 1) p1 (by omega)) a ⊗ₜ b) := by
  subst hk
  rfl

theorem decomp (U : Scheme.{0}) (w : ℤ) :
    (Q1 (J := J) f U w).comp (P1 f U w) + (Q2 (J := J) f U w).comp (P2 f U w) = LinearMap.id := by
  classical
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  obtain ⟨⟨p1, p2⟩, hp⟩ := p
  simp only [LinearMap.add_apply, LinearMap.comp_apply, P1, P2, Q1, Q2, DirectSum.toModule_lof, DirectSum.lmap_lof,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [shiftB (J := J) f U p1 p2 w hp _ (by omega), ← map_add]
  congr 1
  rw [← TensorProduct.add_tmul]
  congr 1
  exact congrArg (fun φ => Sec.map φ a) (mappingCone.id_X f p1 (p1 + 1) rfl)

theorem isTensor (hc : τ.Compat τ' f (𝟙 J) u) (hτ : τ.IsTensor) (hτ' : τ'.IsTensor) : (σ τ τ' f u hc).IsTensor := by
  constructor
  · intro U w y
    obtain ⟨S1, hS1, hP1⟩ := hτ.1 U (w + 1) (Sec.map ((mappingCone.fst u).1.v w (w + 1) rfl) y)
    obtain ⟨S2, hS2, hP2⟩ := hτ'.1 U w (Sec.map ((mappingCone.snd u).v w w (add_zero w)) y)
    refine ⟨S1 ⊓ S2, GrothendieckTopology.intersection_covering _ hS1 hS2, fun V g hg => ?_⟩
    obtain ⟨x1, hx1⟩ := hP1 V g hg.1
    obtain ⟨x2, hx2⟩ := hP2 V g hg.2
    refine ⟨Q1 f V w x1 + Q2 f V w x2, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, etale_mapping_cone_pairing_lift_comp_inl_incl, ← LinearMap.comp_apply ((σ τ τ' f u hc).lift V w), etale_mapping_cone_pairing_lift_comp_inr_incl,
      LinearMap.comp_apply, LinearMap.comp_apply, hx1, hx2, sm_res, sm_res]
    exact congrArg (fun φ => Sec.map φ (Sec.res g y)) (mappingCone.id_X u w (w + 1) rfl)
  · intro U w x hx
    have h1 : τ.lift U (w + 1) (P1 f U w x) = 0 := by
      rw [← LinearMap.comp_apply, etale_mapping_cone_pairing_fst_comp_lift τ τ' f u hc, LinearMap.comp_apply, hx, map_zero]
    have h2 : τ'.lift U w (P2 f U w x) = 0 := by
      rw [← LinearMap.comp_apply, etale_mapping_cone_pairing_snd_comp_lift τ τ' f u hc, LinearMap.comp_apply, hx, map_zero]
    obtain ⟨S1, hS1, hP1⟩ := hτ.2 U (w + 1) _ h1
    obtain ⟨S2, hS2, hP2⟩ := hτ'.2 U w _ h2
    refine ⟨S1 ⊓ S2, GrothendieckTopology.intersection_covering _ hS1 hS2, fun V g hg => ?_⟩
    have e1 : Tens.res g (w + 1) (P1 f U w x) = 0 := hP1 V g hg.1
    have e2 : Tens.res g w (P2 f U w x) = 0 := hP2 V g hg.2
    rw [etale_mapping_cone_tensor_fst_proj_res_comm] at e1
    rw [etale_mapping_cone_tensor_snd_proj_res_comm] at e2
    show Tens.res g w x = 0
    rw [← LinearMap.id_apply (R := ULift.{1} R) (Tens.res g w x), ← decomp (J := J) f V w]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, e1, e2, map_zero, add_zero]

end Tensor

end

end LateralTheory.EtaleFoundations.conePf

theorem LateralTheory.EtaleFoundations.tqis.cone_of : LateralTheory.EtaleFoundations.tqis.cone := by
  intro R _ I I' J T T' τ τ' f u hτ hτ' hc
  exact ⟨LateralTheory.EtaleFoundations.conePf.σ τ τ' f u hc, LateralTheory.EtaleFoundations.conePf.isTensor τ τ' f u hc hτ hτ'⟩
