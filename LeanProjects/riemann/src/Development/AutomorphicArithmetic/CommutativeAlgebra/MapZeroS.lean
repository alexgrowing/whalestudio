import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

noncomputable section

namespace UpperTheory.Kun

variable {R : Type} [CommRing R]

abbrev sh (Q : Cx R) : Cx R := (CategoryTheory.shiftFunctor (Cx R) (-1 : ℤ)).obj Q

abbrev LL (I Q : Cx R) : Cx R := I ⊞ sh Q

def c₁ {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} : Sec ((LL I Q).X s) T →+ Sec (I.X s) T :=
  ((((biprod.fst : LL I Q ⟶ I).f s).hom.app (op T)).hom).toAddMonoidHom

def c₂ {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} : Sec ((LL I Q).X s) T →+ Sec (Q.X (s + -1)) T :=
  ((((biprod.snd : LL I Q ⟶ sh Q).f s).hom.app (op T)).hom).toAddMonoidHom

def cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : Sec ((LL I Q).X s) T :=
  Sec.map ((biprod.inl : I ⟶ LL I Q).f s) a + Sec.map ((biprod.inr : sh Q ⟶ LL I Q).f s) (show Sec ((sh Q).X s) T from b)

def psi (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) (T : Scheme.{0}) (s : ℤ) :
    Sec ((LL I Q).X s) T →+ Sec (I.X s) (W ⨯ T) :=
  AddMonoidHom.mk' (fun x => Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ x) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ x)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z))
    (fun x y => by
      simp only [map_add, LinearMap.add_apply, smul_add]
      abel)

def inL {K I Q : Cx R} {m n : ℤ} (h : m + 1 = n) (α₁ : Cocycle K I n) (α₂ : Cocycle K Q m) : Cocycle K (LL I Q) n :=
  zcomp α₁ (Cocycle.ofHom (biprod.inl : I ⟶ LL I Q)) (add_zero n) +
    ((n.negOnePow : ℤˣ) : ℤ) • zcomp (α₂.rightShift (-1) n (by omega)) (Cocycle.ofHom (biprod.inr : sh Q ⟶ LL I Q)) (add_zero n)

def sg {X : Scheme.{0}} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj (sch.obj X)) I n) : Sec (I.X n) X :=
  ev α.1 0 n (by simp) X (𝟙 X)

end UpperTheory.Kun

namespace UpperTheory.Kun
variable {R : Type} [CommRing R]

theorem res_id {F : Shv R} {X : Scheme.{0}} (b : Sec F X) : Sec.res (𝟙 X) b = b := by
  change (F.obj.map (𝟙 (op X))).hom b = b
  rw [F.obj.map_id]
  rfl

theorem res_res {F : Shv R} {X Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) (b : Sec F X) :
    Sec.res g (Sec.res f b) = Sec.res (g ≫ f) b := by
  change _ = (F.obj.map (f.op ≫ g.op)).hom b
  rw [F.obj.map_comp]
  rfl

theorem map_map {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := rfl

theorem map_idS {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem map_zeroS {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem map_addS {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (ConcreteCategory.congr_hom (φ.hom.naturality g.op) x).symm

theorem c₁_cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : c₁ (cc (I := I) (Q := Q) a b) = a := by
  have h1 : ((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.fst : LL I Q ⟶ I).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, biprod.inl_fst, HomologicalComplex.id_f]
  have h2 : ((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.fst : LL I Q ⟶ I).f s) = 0 := by
    rw [← HomologicalComplex.comp_f, biprod.inr_fst, HomologicalComplex.zero_f]
  unfold cc
  rw [map_add]
  change Sec.map _ (Sec.map _ a) + Sec.map _ (Sec.map _ _) = a
  rw [map_map, map_map, h1, h2, map_idS, map_zeroS, add_zero]

theorem c₂_cc {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (a : Sec (I.X s) T) (b : Sec (Q.X (s + -1)) T) : c₂ (cc (I := I) (Q := Q) a b) = b := by
  have h1 : ((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s) = 0 := by
    rw [← HomologicalComplex.comp_f, biprod.inl_snd, HomologicalComplex.zero_f]
  have h2 : ((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, biprod.inr_snd, HomologicalComplex.id_f]
  unfold cc
  rw [map_add]
  change (Sec.map (((biprod.inl : I ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s)) a +
    Sec.map (((biprod.inr : sh Q ⟶ LL I Q).f s) ≫ ((biprod.snd : LL I Q ⟶ sh Q).f s)) (show Sec ((sh Q).X s) T from b) : Sec ((sh Q).X s) T) = b
  rw [h1, h2, map_zeroS, zero_add]
  rfl

theorem cc_c {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (x : Sec ((LL I Q).X s) T) : cc (c₁ x) (c₂ x) = x := by
  have h : ((biprod.fst : LL I Q ⟶ I).f s) ≫ ((biprod.inl : I ⟶ LL I Q).f s) +
      ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  change Sec.map _ (Sec.map _ x) + Sec.map _ (Sec.map _ x) = x
  rw [map_map, map_map, ← map_addS, h, map_idS]

theorem LLsec_ext {I Q : Cx R} {T : Scheme.{0}} {s : ℤ} (x y : Sec ((LL I Q).X s) T) (h₁ : c₁ x = c₁ y) (h₂ : c₂ x = c₂ y) : x = y := by
  rw [← cc_c x, ← cc_c y, h₁, h₂]

theorem c₁_res {I Q : Cx R} {V T : Scheme.{0}} {s : ℤ} (g : V ⟶ T) (x : Sec ((LL I Q).X s) T) : c₁ (Sec.res g x) = Sec.res g (c₁ x) :=
  (res_map _ g x).symm

theorem c₂_res {I Q : Cx R} {V T : Scheme.{0}} {s : ℤ} (g : V ⟶ T) (x : Sec ((LL I Q).X s) T) : c₂ (Sec.res g x) = Sec.res g (c₂ x) :=
  (res_map ((biprod.snd : LL I Q ⟶ sh Q).f s) g x).symm

theorem c₁_d {I Q : Cx R} {T : Scheme.{0}} (s t : ℤ) (x : Sec ((LL I Q).X s) T) : c₁ (Sec.map ((LL I Q).d s t) x) = Sec.map (I.d s t) (c₁ x) := by
  change Sec.map _ (Sec.map _ x) = Sec.map _ (Sec.map _ x)
  rw [map_map, map_map, (biprod.fst : LL I Q ⟶ I).comm]

theorem sh_d (Q : Cx R) (s t : ℤ) : (sh Q).d s t = - Q.d (s + -1) (t + -1) := by
  have : (sh Q).d s t = (-1 : ℤ).negOnePow • Q.d (s + -1) (t + -1) := CochainComplex.shiftFunctor_obj_d' _ _ _ _
  rw [this]
  simp

theorem c₂_d {I Q : Cx R} {T : Scheme.{0}} (s t : ℤ) (x : Sec ((LL I Q).X s) T) :
    c₂ (Sec.map ((LL I Q).d s t) x) = - Sec.map (Q.d (s + -1) (t + -1)) (c₂ x) := by
  have h := (biprod.snd : LL I Q ⟶ sh Q).comm s t
  have e : ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ (sh Q).d s t =
      -(((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ (show (sh Q).X s ⟶ (sh Q).X t from Q.d (s + -1) (t + -1))) := by
    rw [sh_d]
    exact Preadditive.comp_neg _ _
  change Sec.map _ (Sec.map _ x) = _
  rw [map_map, ← h, e]
  rfl

theorem sg_pull {X Y : Scheme.{0}} {I : Cx R} {n : ℤ} (f : Y ⟶ X) (α : Cocycle ((chains R).obj (sch.obj X)) I n) :
    sg (zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)) = Sec.res f (sg α) := by
  have h1 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).2.2.2.1 (sch.map f) α.1 0 n (by simp) Y (𝟙 Y)
  have h2 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).2.1 α.1 0 n (by simp) Y X f (𝟙 X)
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1

theorem sg_sub {X : Scheme.{0}} {I : Cx R} {n : ℤ} (α β : Cocycle ((chains R).obj (sch.obj X)) I n) : sg (α - β) = sg α - sg β :=
  ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 α.1 β.1 0 n (by simp) X (𝟙 X)).2.1

theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y :=
  map_add _ _ _

theorem res_units {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (ε : ℤˣ) (x : Sec F U) : Sec.res g (ε • x) = ε • Sec.res g x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

theorem psi_nat (W : Scheme.{0}) {I Q P : Cx R} (μ : Pair Q P I) (z : Sec (P.X 1) W) {T' T : Scheme.{0}} (g : T' ⟶ T) (s : ℤ)
    (a : Sec ((LL I Q).X s) T) : Sec.res (prod.map (𝟙 W) g) (psi W μ z T s a) = psi W μ z T' s (Sec.res g a) := by
  change Sec.res (prod.map (𝟙 W) g) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₁ a) +
      s.negOnePow • μ.mul (W ⨯ T) (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T ⟶ T) (c₂ a)) (Sec.res (prod.fst : W ⨯ T ⟶ W) z)) =
    Sec.res (prod.snd : W ⨯ T' ⟶ T') (c₁ (Sec.res g a)) +
      s.negOnePow • μ.mul (W ⨯ T') (s + -1) 1 s (by omega) (Sec.res (prod.snd : W ⨯ T' ⟶ T') (c₂ (Sec.res g a))) (Sec.res (prod.fst : W ⨯ T' ⟶ W) z)
  rw [res_add, res_units, μ.nat, c₁_res, c₂_res, res_res, res_res, res_res, res_res, res_res]
  simp

theorem LL_inj {I Q : Cx R} (hI : ∀ s, Injective (I.X s)) (hQ : ∀ s, Injective (Q.X s)) (s : ℤ) : Injective ((LL I Q).X s) := by
  have hQ' : Injective ((sh Q).X s) := hQ (s + -1)
  have h : ((biprod.fst : LL I Q ⟶ I).f s) ≫ ((biprod.inl : I ⟶ LL I Q).f s) +
      ((biprod.snd : LL I Q ⟶ sh Q).f s) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f s) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  refine ⟨fun {X Y} g f _ => ?_⟩
  haveI := hI s
  obtain ⟨h₁, e₁⟩ := Injective.factors (g ≫ (biprod.fst : LL I Q ⟶ I).f s) f
  obtain ⟨h₂, e₂⟩ := Injective.factors (g ≫ (biprod.snd : LL I Q ⟶ sh Q).f s) f
  refine ⟨h₁ ≫ (biprod.inl : I ⟶ LL I Q).f s + h₂ ≫ (biprod.inr : sh Q ⟶ LL I Q).f s, ?_⟩
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, e₁, e₂, Category.assoc, Category.assoc, ← Preadditive.comp_add, h, Category.comp_id]

theorem LL_ge (I Q : Cx R) [I.IsStrictlyGE 0] [Q.IsStrictlyGE 0] : (LL I Q).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hI := I.isZero_of_isStrictlyGE 0 i hi
  have hQ : IsZero ((sh Q).X i) := Q.isZero_of_isStrictlyGE 0 (i + -1) (by omega)
  have h : ((biprod.fst : LL I Q ⟶ I).f i) ≫ ((biprod.inl : I ⟶ LL I Q).f i) +
      ((biprod.snd : LL I Q ⟶ sh Q).f i) ≫ ((biprod.inr : sh Q ⟶ LL I Q).f i) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply, biprod.total, HomologicalComplex.id_f]
  rw [IsZero.iff_id_eq_zero, ← h, hI.eq_of_tgt ((biprod.fst : LL I Q ⟶ I).f i) 0, hQ.eq_of_tgt ((biprod.snd : LL I Q ⟶ sh Q).f i) 0]
  simp
  exact zero_comp

end UpperTheory.Kun
