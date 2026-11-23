import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexPairingTensorUniversalPropertyStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section

namespace GlobalTheory.EtC.TensUniv

variable {R : Type} [CommRing R]

def tof {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) : Tens I J U w :=
  DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)

theorem tens_ind {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (P : Tens I J U w → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (ht : ∀ p a b, P (tof p a b)) (x : Tens I J U w) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | of p z =>
    induction z using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => exact ht p a b
    | add z z' hz hz' => simpa [map_add] using hadd _ _ hz hz'
  | add x y hx hy => exact hadd x y hx hy

theorem lift_tof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (tof p a b) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift tof
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  convert DirectSum.toModule_lof (ULift.{1} R) (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)
  simp

theorem res_tof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (tof p a b) = tof p (Sec.res g a) (Sec.res g b) := by
  unfold Tens.res tof
  rw [DirectSum.lmap_of]
  rfl

theorem map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (y : Sec F U) :
    Sec.map (φ ≫ ψ) y = Sec.map ψ (Sec.map φ y) := rfl

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := φ.hom.naturality g.op
  exact (congrArg (fun k => k.hom y) this).symm

theorem shv_ext {F G : Shv R} (φ ψ : F ⟶ G) (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  exact h U.unop a

end GlobalTheory.EtC.TensUniv

namespace GlobalTheory.EtC.TensUniv

variable {R : Type} [CommRing R]

def tmap {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Tens I' J' U w :=
  DirectSum.lmap fun p => TensorProduct.map ((f.f p.1.1).hom.app (op U)).hom ((g.f p.1.2).hom.app (op U)).hom

theorem tmap_tof {I J I' J' : Cx R} (f : I ⟶ I') (g : J ⟶ J') (U : Scheme.{0}) {w : ℤ}
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    tmap f g U w (tof p a b) = tof p (Sec.map (f.f p.1.1) a) (Sec.map (g.f p.1.2) b) := by
  unfold tmap tof
  rw [DirectSum.lmap_of]
  rfl

def mkHom {F G : Shv R} (φ : ∀ U : Scheme.{0}, Sec F U →ₗ[ULift.{1} R] Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom (φ U.unop)
      naturality := fun U V g => by
        ext y
        exact (hφ V.unop U.unop g.unop y).symm }

theorem eq_of_lift {I J K : Cx R} {τ : Pair I J K} (hτ : τ.IsTensor) {w : ℤ} {M : Shv R}
    (c c' : ∀ U : Scheme.{0}, Sec (K.X w) U → Sec M U)
    (hc : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V (Sec.res g y))
    (hc' : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c' U y) = c' V (Sec.res g y))
    (h : ∀ V x, c V (τ.lift V w x) = c' V (τ.lift V w x)) (U : Scheme.{0}) (y : Sec (K.X w) U) :
    c U y = c' U y := by
  refine (sec_ext_glue R M U).1 _ _ (loc_mono U _ _ (hτ.1 U w y) ?_)
  rintro V g ⟨x, hx⟩
  rw [hc, hc', ← hx, h]

theorem exists_hom {I J K : Cx R} {τ : Pair I J K} (hτ : τ.IsTensor) (w : ℤ) (M : Shv R)
    (b : ∀ U : Scheme.{0}, Tens I J U w →ₗ[ULift.{1} R] Sec M U)
    (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) :
    ∃ m : K.X w ⟶ M, ∀ U x, Sec.map m (τ.lift U w x) = b U x := by
  obtain ⟨φ, hφn, hφl⟩ := GlobalTheory.T.sheafComplexPairing_tensor_universal_property R R τ hτ w M (fun U => (b U).toAddMonoidHom) hb
  have hsmul : ∀ U (r : ULift.{1} R) (y : Sec (K.X w) U), φ U (r • y) = r • φ U y := by
    intro U r
    refine eq_of_lift hτ (fun U y => φ U (r • y)) (fun U y => r • φ U y) ?_ ?_ ?_ U
    · intro V U g y
      rw [hφn]
      congr 1
      exact map_smul _ _ _
    · intro V U g y
      rw [← hφn]
      exact map_smul _ _ _
    · intro V x
      rw [← map_smul (τ.lift V w) r x, hφl, hφl]
      exact map_smul (b V) r x
  exact ⟨mkHom (fun U => { toFun := φ U, map_add' := map_add _, map_smul' := hsmul U }) hφn, fun U x => hφl U x⟩

end GlobalTheory.EtC.TensUniv

namespace GlobalTheory.EtC.TensUniv

variable {R : Type} [CommRing R]

theorem map_add' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem map_usmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (u : ℤˣ) (x : Sec F U) :
    Sec.map φ (u • x) = u • Sec.map φ x := by
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul _ _ _

theorem lin_nat {I J I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ) (V U : Scheme.{0})
    (k : V ⟶ U) (x : Tens I J U w) :
    Sec.res k ((ν.lift U w ∘ₗ tmap f g U w) x) = (ν.lift V w ∘ₗ tmap f g V w) (Tens.res k w x) := by
  induction x using tens_ind with
  | h0 => simp
  | hadd x y hx hy => simp only [map_add]; exact congrArg₂ (· + ·) hx hy
  | ht p a b =>
    simp only [LinearMap.comp_apply, res_tof, tmap_tof, lift_tof]
    rw [ν.nat, res_map, res_map]

theorem compat_of {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') {w : ℤ}
    (m : K.X w ⟶ K'.X w) (hm : ∀ U x, Sec.map m (τ.lift U w x) = (ν.lift U w ∘ₗ tmap f g U w) x)
    (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map m (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b) := by
  have := hm U (tof ⟨(s, t), h⟩ a b)
  rwa [lift_tof, LinearMap.comp_apply, tmap_tof, lift_tof] at this

theorem map_d {I I' : Cx R} (f : I ⟶ I') (s : ℤ) {U : Scheme.{0}} (a : Sec (I.X s) U) :
    Sec.map (f.f (s + 1)) (Sec.map (I.d s (s + 1)) a) = Sec.map (I'.d s (s + 1)) (Sec.map (f.f s) a) := by
  rw [← map_comp', ← map_comp', f.comm]

theorem part1 {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) {I' J' K' : Cx R} (ν : Pair I' J' K')
    (f : I ⟶ I') (g : J ⟶ J') : ∃! u : K ⟶ K', τ.Compat ν f g u := by
  have hex : ∀ w, ∃ m : K.X w ⟶ K'.X w, ∀ U x, Sec.map m (τ.lift U w x) = (ν.lift U w ∘ₗ tmap f g U w) x :=
    fun w => exists_hom hτ w (K'.X w) (fun U => ν.lift U w ∘ₗ tmap f g U w) (lin_nat ν f g w)
  choose m hm using hex
  have hc : ∀ w U s t (h : s + t = w) a b,
      Sec.map (m w) (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b) :=
    fun w U s t h a b => compat_of τ ν f g (m w) (hm w) U s t h a b
  let u : K ⟶ K' :=
    { f := m
      comm' := by
        rintro i j (rfl : i + 1 = j)
        apply shv_ext
        intro U y
        rw [map_comp', map_comp']
        refine eq_of_lift hτ (fun U y => Sec.map (K'.d i (i + 1)) (Sec.map (m i) y))
          (fun U y => Sec.map (m (i + 1)) (Sec.map (K.d i (i + 1)) y)) ?_ ?_ ?_ U y
        · intro V U k y
          rw [res_map, res_map]
        · intro V U k y
          rw [res_map, res_map]
        · intro V x
          induction x using tens_ind with
          | h0 => simp
          | hadd x y hx hy => simp only [map_add]; exact congrArg₂ (· + ·) hx hy
          | ht p a b =>
            simp only [lift_tof]
            rw [hc, ν.leibniz, τ.leibniz, map_add', map_usmul, hc, hc, map_d f, map_d g] }
  refine ⟨u, fun U s t w h a b => hc w U s t h a b, fun u' hu' => ?_⟩
  apply HomologicalComplex.hom_ext
  intro w
  apply shv_ext
  intro U y
  refine eq_of_lift hτ (fun U y => Sec.map (u'.f w) y) (fun U y => Sec.map (m w) y)
    (fun V U k y => res_map _ k y) (fun V U k y => res_map _ k y) ?_ U y
  intro V x
  induction x using tens_ind with
  | h0 => simp
  | hadd x y hx hy => simp only [map_add]; exact congrArg₂ (· + ·) hx hy
  | ht p a b =>
    simp only [lift_tof]
    rw [hu', hc]

theorem part3 {I J K K' : Cx R} (τ : Pair I J K) (u : K ⟶ K') : ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u := by
  refine ⟨⟨fun U s t w h => (τ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    simp only [LinearMap.compr₂_apply]
    exact (res_map (u.f w) g _).trans (congrArg _ (τ.nat g s t w h a b))
  · intro U s t w h a b
    simp only [LinearMap.compr₂_apply]
    have hu : ∀ z : Sec (K.X w) U,
        Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) z) = Sec.map (u.f (w + 1)) (Sec.map (K.d w (w + 1)) z) := by
      intro z
      rw [← map_comp', ← map_comp', u.comm]
    refine (hu _).trans ?_
    rw [τ.leibniz, map_add', map_usmul]
  · intro U s t w h a b
    rfl

theorem sec_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h := hF.eq_of_src (𝟙 F) (mkHom (fun _ => 0) (fun V U g y => by simp))
  have : Sec.map (𝟙 F) a = Sec.map (mkHom (fun _ => 0) (fun V U g y => by simp)) a := by rw [h]
  exact this

theorem part2 {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) (hI : I.IsStrictlyGE 0) (hJ : J.IsStrictlyGE 0) :
    K.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff] at hI hJ ⊢
  intro w hw
  have hz : ∀ (V : Scheme.{0}) (x : Tens I J V w), x = 0 := by
    intro V x
    induction x using tens_ind with
    | h0 => rfl
    | hadd x y hx hy => rw [hx, hy, add_zero]
    | ht p a b =>
      rcases lt_or_ge p.1.1 0 with h1 | h1
      · rw [sec_zero_of_isZero (hI _ h1) a]
        simp [tof]
      · have h2 : p.1.2 < 0 := by have := p.2; omega
        rw [sec_zero_of_isZero (hJ _ h2) b]
        simp [tof]
  have hsec : ∀ U (y : Sec (K.X w) U), y = 0 := by
    intro U y
    refine (sec_ext_glue R _ U).1 _ _ (loc_mono U _ _ (hτ.1 U w y) ?_)
    rintro V g ⟨x, hx⟩
    rw [← hx, hz V x, map_zero]
    simp
  rw [IsZero.iff_id_eq_zero]
  apply shv_ext
  intro U a
  rw [hsec U a]
  simp

end GlobalTheory.EtC.TensUniv

theorem GlobalTheory.EtC.Pair.isTensor_universal : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧
    (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧
    ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u := by
  intro R _ I J K τ hτ
  exact ⟨fun ν f g => GlobalTheory.EtC.TensUniv.part1 τ hτ ν f g, fun hI hJ => GlobalTheory.EtC.TensUniv.part2 τ hτ hI hJ,
    fun u => GlobalTheory.EtC.TensUniv.part3 τ u⟩
