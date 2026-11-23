import Development.EtaleCohomology.TateTwists.acycPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R]

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h; exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  have H : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → ∃ T : Sieve V, T ∈ Scheme.etaleTopology V ∧
      ∀ (W : Scheme.{0}) (k : W ⟶ V), T.arrows k → Q W (k ≫ g) := fun V g hg => hPQ V g (hP V g hg)
  choose T hT hQ using H
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g hg W k hk

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have := congrArg (fun f => f.hom x) (φ.hom.naturality g.op)
  simpa [Sec.map, Sec.res] using this.symm

theorem map_dd {C : Cx R} {U : Scheme.{0}} (i j k : ℤ) (x : Sec (C.X i) U) :
    Sec.map (C.d j k) (Sec.map (C.d i j) x) = 0 := by
  change ((C.d i j ≫ C.d j k).hom.app (op U)).hom x = 0
  rw [C.d_comp_d]; simp

theorem sec_zero {C : Cx R} (a : ℤ) [C.IsStrictlyGE a] {s : ℤ} (hs : s < a) {U : Scheme.{0}}
    (x : Sec (C.X s) U) : x = 0 := by
  have hz := C.isZero_of_isStrictlyGE a s hs
  have := congrArg (fun f : C.X s ⟶ C.X s => (f.hom.app (op U)).hom x) (hz.eq_of_src (𝟙 _) 0)
  simpa using this

theorem tens_zero {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} R) M]
    [Module (ULift.{1} R) N] (hM : ∀ m : M, m = 0) (x : M ⊗[ULift.{1} R] N) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [hM m, TensorProduct.zero_tmul]
  | add a b ha hb => rw [ha, hb, add_zero]

abbrev Ix (w : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = w}

variable {C J T : Cx R}

abbrev Cmp (C J : Cx R) (U : Scheme.{0}) (w : ℤ) : Ix w → Type 1 :=
  fun q => Sec (C.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U

def Dm (U : Scheme.{0}) (w w' : ℤ) (hw : w + 1 = w') : Tens C J U w →ₗ[ULift.{1} R] Tens C J U w' := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof (ULift.{1} R) (Ix w') (Cmp C J U w') ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map ((C.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
    ((p.1.1.negOnePow : ℤ)) • (DirectSum.lof (ULift.{1} R) (Ix w') (Cmp C J U w')
      ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

theorem Dm_lof (U : Scheme.{0}) (w w' : ℤ) (hw : w + 1 = w') (p : Ix w) (v : Cmp C J U w p) :
    Dm U w w' hw (DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) p v) =
      DirectSum.lof (ULift.{1} R) (Ix w') (Cmp C J U w') ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
        (TensorProduct.map ((C.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id v) +
      ((p.1.1.negOnePow : ℤ)) • DirectSum.lof (ULift.{1} R) (Ix w') (Cmp C J U w')
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
        (TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom v) := by
  classical
  unfold Dm
  convert DirectSum.toModule_lof (ULift.{1} R) p v using 1
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]

theorem lift_lof (τ : Pair C J T) (U : Scheme.{0}) (w : ℤ) (p : Ix w) (a : Sec (C.X p.1.1) U)
    (b : Sec (J.X p.1.2) U) :
    τ.lift U w (DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  classical
  unfold Pair.lift
  convert DirectSum.toModule_lof (ULift.{1} R) (M := Cmp C J U w) p (a ⊗ₜ[ULift.{1} R] b) using 1
  simp

theorem lift_Dm (τ : Pair C J T) (U : Scheme.{0}) (w : ℤ) (x : Tens C J U w) :
    τ.lift U (w + 1) (Dm U w (w + 1) rfl x) = Sec.map (T.d w (w + 1)) (τ.lift U w x) := by
  classical
  have : (τ.lift U (w + 1)) ∘ₗ Dm U w (w + 1) rfl = ((T.d w (w + 1)).hom.app (op U)).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply, Dm_lof, map_add, map_zsmul, TensorProduct.map_tmul, LinearMap.id_apply]
    erw [lift_lof, lift_lof, lift_lof]
    have := τ.leibniz U p.1.1 p.1.2 w p.2 a b
    simp only [Sec.map] at this
    rw [this, Units.smul_def]
  exact LinearMap.congr_fun this x

theorem lift_res (τ : Pair C J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) :
    τ.lift V w (Tens.res g w x) = Sec.res g (τ.lift U w x) := by
  classical
  have : (τ.lift V w) ∘ₗ Tens.res g w = ((T.X w).obj.map g.op).hom ∘ₗ τ.lift U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply, Tens.res]
    rw [DirectSum.lmap_lof, TensorProduct.map_tmul]
    rw [lift_lof, lift_lof]
    exact (τ.nat g p.1.1 p.1.2 w p.2 a b).symm
  exact LinearMap.congr_fun this x

end LateralTheory.EtaleFoundations.stairPf
