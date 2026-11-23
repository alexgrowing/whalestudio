import Development.EtaleCohomology.KummerTheory.FinalTheorems

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ConeAlgPf
open LateralTheory.KummerTheory.LHCut

variable {Λ : Type} [CommRing Λ]

theorem sres_comp {F : Shv Λ} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res h (Sec.res g a) = Sec.res (h ≫ g) a := by
  show (F.obj.map h.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (h ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]
  rfl

theorem smap_res {F G : Shv Λ} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
  (congrArg (fun k => k.hom a) (φ.hom.naturality g.op)).symm

theorem smap_comp {F G H : Shv Λ} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map ψ (Sec.map φ a) = Sec.map (φ ≫ ψ) a := rfl

theorem dd {C : Cx Λ} (i j k : ℤ) {U : Scheme.{0}} (a : Sec (C.X i) U) :
    Sec.map (C.d j k) (Sec.map (C.d i j) a) = 0 := by
  rw [smap_comp, HomologicalComplex.d_comp_d]; rfl

theorem leib' {I J K : Cx Λ} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U)
    (b : Sec (J.X t) U) (ha : Sec.map (I.d s (s + 1)) a = 0) (t' w' : ℤ) (ht : t + 1 = t') (hw : w + 1 = w') :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst ht; subst hw
  rw [μ.leibniz, ha, map_zero, LinearMap.zero_apply, zero_add]

theorem rst_fst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ pullback.fst p U.hom = pullback.fst p V.hom := by
  simp only [rst, pullback.map]; erw [pullback.lift_fst]; simp

theorem rst_snd {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ pullback.snd p U.hom = pullback.snd p V.hom ≫ g.left := by
  simp only [rst, pullback.map]; erw [pullback.lift_snd]

theorem rst_comp {X S : Scheme.{0}} (p : X ⟶ S) {W V U : Over S} (g' : W ⟶ V) (g : V ⟶ U) :
    rst p (g' ≫ g) = rst p g' ≫ rst p g := by
  apply pullback.hom_ext
  · rw [Category.assoc, rst_fst, rst_fst, rst_fst]
  · rw [Category.assoc, rst_snd, rst_snd, ← Category.assoc, rst_snd, Category.assoc, Over.comp_left]

theorem smap_add {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _
theorem smap_sub {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _
theorem smap_smul {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (c : ULift.{1} Λ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_smul _ _ _
theorem smap_sum {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (t : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ t, f i) = ∑ i ∈ t, Sec.map φ (f i) := map_sum _ _ _
theorem sres_sub {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _
theorem sres_zero {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _
theorem sres_sum {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) {ι : Type*} (t : Finset ι) (f : ι → Sec F U) :
    Sec.res g (∑ i ∈ t, f i) = ∑ i ∈ t, Sec.res g (f i) := map_sum _ _ _

section Main
variable {I J K : Cx Λ} {r : ℕ → ℕ} {M : ℕ}

theorem usmul_map {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (u : ℤˣ) (a : Sec F U) :
    Sec.map φ (u • a) = u • Sec.map φ a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem usmul_res {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (a : Sec F U) :
    Sec.res g (u • a) = u • Sec.res g a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem dS_add (n m : ℤ) {U : Scheme.{0}} (b b' : FinalTheorems J r M n U) : dS n m (b + b') = dS n m b + dS n m b' := by
  funext a s
  simp only [dS, Pi.add_apply]
  rw [smap_add, smul_add]

theorem dS_smul (n m : ℤ) {U : Scheme.{0}} (c : ULift.{1} Λ) (b : FinalTheorems J r M n U) : dS n m (c • b) = c • dS n m b := by
  funext a s
  simp only [dS, Pi.smul_apply]
  rw [smap_smul, Units.smul_def, Units.smul_def, smul_comm]

theorem dS_dS (n m k : ℤ) {U : Scheme.{0}} (b : FinalTheorems J r M n U) : dS m k (dS n m b) = 0 := by
  funext a s
  simp only [dS, Pi.zero_apply]
  rw [usmul_map, dd, smul_zero, smul_zero]

variable (μ : Pair I J K) {X S : Scheme.{0}} (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem Phi_add (n w : ℤ) (h : n = w) (U : Over S) (b b' : FinalTheorems J r M n U.left) :
    Phi μ p γ n w h U (b + b') = Phi μ p γ n w h U b + Phi μ p γ n w h U b' := by
  simp only [Phi, Pi.add_apply, map_add, Finset.sum_add_distrib]

theorem Phi_smul (n w : ℤ) (h : n = w) (U : Over S) (c : ULift.{1} Λ) (b : FinalTheorems J r M n U.left) :
    Phi μ p γ n w h U (c • b) = c • Phi μ p γ n w h U b := by
  simp only [Phi, Pi.smul_apply, map_smul, Finset.smul_sum]

theorem d_Phi (hγ : Closed γ) (n w : ℤ) (h : n = w) (n' w' : ℤ) (hn : n + 1 = n') (hw : w + 1 = w') (U : Over S)
    (b : FinalTheorems J r M n U.left) :
    Sec.map (K.d w w') (Phi μ p γ n w h U b) = Phi μ p γ n' w' (by omega) U (dS n n' b) := by
  simp only [Phi, dS]
  rw [smap_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [smap_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have ha : Sec.map (I.d ((a : ℕ) : ℤ) ((a : ℕ) + 1)) (Sec.res (pullback.fst p U.hom) (γ a s)) = 0 := by
    rw [← smap_res, hγ]; exact sres_zero _
  rw [leib' μ _ _ _ _ _ _ _ ha (n' - ((a : ℕ) : ℤ)) w' (by omega) hw, usmul_res, smap_res, Units.smul_def,
    Units.smul_def, map_zsmul]

theorem Phi_res (n w : ℤ) (h : n = w) {V U : Over S} (g : V ⟶ U) (b : FinalTheorems J r M n U.left) :
    Sec.res (rst p g) (Phi μ p γ n w h U b) = Phi μ p γ n w h V (fun a s => Sec.res g.left (b a s)) := by
  simp only [Phi]
  rw [sres_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sres_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [μ.nat, sres_comp, sres_comp, sres_comp, rst_fst, rst_snd]

end Main

theorem coneAlg_of : ConeAlg := by
  intro Λ _ I J K μ X S p r M γ hγ j j' h U
  refine ⟨⟨fun x y => ?_, fun c x => ?_⟩, fun j'' h' x => ?_, fun V g => ⟨⟨fun x y => ?_, fun c x => ?_⟩, fun x => ?_,
    fun W g' x => ?_⟩⟩
  · refine Prod.ext (dS_add _ _ _ _) ?_
    show Phi μ p γ _ _ h U (x.1 + y.1) - Sec.map (K.d j j') (x.2 + y.2) = _
    rw [Phi_add, smap_add, add_sub_add_comm]; rfl
  · refine Prod.ext (dS_smul _ _ _ _) ?_
    show Phi μ p γ _ _ h U (c • x.1) - Sec.map (K.d j j') (c • x.2) = _
    rw [Phi_smul, smap_smul, ← smul_sub]; rfl
  · refine Prod.ext (dS_dS _ _ _ _) ?_
    show Phi μ p γ _ _ h' U (dS _ _ x.1) - Sec.map (K.d j' j'') (Phi μ p γ _ _ h U x.1 - Sec.map (K.d j j') x.2) = 0
    rw [smap_sub, d_Phi μ p γ hγ (j + 1) j' h (j' + 1) j'' (by omega) h', dd, sub_zero, sub_self]
  · refine Prod.ext ?_ (map_add _ _ _)
    funext a s; exact map_add _ _ _
  · refine Prod.ext ?_ (map_smul _ _ _)
    funext a s; exact map_smul _ _ _
  · refine Prod.ext ?_ ?_
    · funext a s
      show Sec.res g.left (_ • Sec.map _ _) = _ • Sec.map _ (Sec.res g.left _)
      rw [usmul_res, smap_res]
    · show Sec.res (rst p g) (Phi μ p γ _ _ h U x.1 - Sec.map (K.d j j') x.2) =
        Phi μ p γ _ _ h V (fun a s => Sec.res g.left (x.1 a s)) - Sec.map (K.d j j') (Sec.res (rst p g) x.2)
      rw [sres_sub, Phi_res, smap_res]
  · refine Prod.ext ?_ ?_
    · funext a s
      show Sec.res (g' ≫ g).left _ = Sec.res g'.left (Sec.res g.left _)
      rw [Over.comp_left, sres_comp]
    · show Sec.res (rst p (g' ≫ g)) x.2 = Sec.res (rst p g') (Sec.res (rst p g) x.2)
      rw [rst_comp, sres_comp]

end LateralTheory.KummerTheory.ConeAlgPf
