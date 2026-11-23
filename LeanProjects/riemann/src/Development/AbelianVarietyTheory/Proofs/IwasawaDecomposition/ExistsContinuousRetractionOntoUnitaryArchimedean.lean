import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def evGL (w : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℂ) w)

theorem gl_ext_evGL {a b : GL (Fin n) (Cinf E)} (h : ∀ w, evGL w a = evGL w b) : a = b := by
  ext i j w
  exact congrArg (fun x : GL (Fin n) ℂ => x i j) (h w)

open Classical in

def atPlace (v : InfinitePlace E) : Cinf E →ₙ+* Cinf E where
  toFun x := Pi.single v (x v)
  map_mul' x y := Pi.single_mul (α := fun _ : InfinitePlace E => ℂ) v (x v) (y v)
  map_zero' := Pi.single_zero (M := fun _ : InfinitePlace E => ℂ) v
  map_add' x y := Pi.single_add (f := fun _ : InfinitePlace E => ℂ) v (x v) (y v)

theorem atPlace_self (v : InfinitePlace E) (x : Cinf E) : atPlace v x v = x v := by
  classical
  exact Pi.single_eq_same (M := fun _ : InfinitePlace E => ℂ) v (x v)

theorem atPlace_of_ne {v w : InfinitePlace E} (h : w ≠ v) (x : Cinf E) : atPlace v x w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun _ : InfinitePlace E => ℂ) h (x v)

def cutGL (v : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) (Cinf E) := cornerGL n (atPlace v)

theorem evGL_cutGL_self (v : InfinitePlace E) (y : GL (Fin n) (Cinf E)) : evGL v (cutGL v y) = evGL v y :=
  map_cornerGL_of_hom _ _ _ (fun x => atPlace_self v x) y

theorem evGL_cutGL_of_ne {v w : InfinitePlace E} (h : w ≠ v) (y : GL (Fin n) (Cinf E)) :
    evGL w (cutGL v y) = 1 :=
  map_cornerGL_of_zero _ _ (fun x => atPlace_of_ne h x) y

theorem unitary_iff_evGL (y : GL (Fin n) (Cinf E)) :
    y.valᴴ * y.val = 1 ↔ ∀ w, (evGL w y).valᴴ * (evGL w y).val = 1 := by
  have key : ∀ (w : InfinitePlace E) i j, ((evGL w y).valᴴ * (evGL w y).val) i j = (y.valᴴ * y.val) i j w := by
    intro w i j
    simp [evGL, Matrix.mul_apply, Finset.sum_apply]
  constructor
  · intro h w
    ext i j
    rw [key, h]
    rcases eq_or_ne i j with rfl | e <;> simp [*]
  · intro h
    ext i j w
    rw [← key, h w]
    rcases eq_or_ne i j with rfl | e <;> simp [*]

theorem cInf_unitary (g : UA E n) : (cInf g).valᴴ * (cInf g).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [mul_one] at hg
  have h1 : (cInf g).val = g.1.val.map (pInf E) := rfl
  have h3 : (cT (conjAd E) g.1.val).map (pInf E) = (cInf g).valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, h1]
    exact (infEq E).symm_apply_apply _
  have h5 := congrArg (fun m => m.map (pInf E)) hg
  simp only [Matrix.map_mul, h3, ← h1] at h5
  rw [h5]
  ext1 i j
  rcases eq_or_ne i j with rfl | e <;> simp [*]

theorem continuous_pInfComp : Continuous (pInf E) := by
  have h : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_cInf : Continuous (cInf : UA E n → GL (Fin n) (Cinf E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map continuous_pInfComp)).comp continuous_subtype_val

theorem continuous_cutGL (v : InfinitePlace E) : Continuous (cutGL v : GL (Fin n) (Cinf E) → _) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (atPlace v : Cinf E → Cinf E) :=
    continuous_pi fun w => by
      by_cases h : w = v
      · subst h
        exact (show Continuous fun x : Cinf E => x w from continuous_apply w).congr
          fun x => (atPlace_self w x).symm
      · exact continuous_const.congr fun x => (atPlace_of_ne h x).symm
  exact continuous_const.sub (continuous_const) |>.add (continuous_id.matrix_map hs)

theorem continuous_infGL : Continuous (infGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) :=
    (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub (continuous_const) |>.add (continuous_id.matrix_map hs)

theorem coord_embedding (w : InfinitePlace E) : coord w.embedding = Pi.evalRingHom (fun _ => ℂ) w := by
  have h := InfinitePlace.mk_embedding w
  unfold coord
  rw [if_pos (by rw [h]), h]

theorem map_coord_of_evGL (τ : E →+* ℂ) {y : GL (Fin n) (Cinf E)} (h : evGL (InfinitePlace.mk τ) y = 1) :
    GeneralLinearGroup.map (coord τ) y = 1 := by
  unfold coord
  split_ifs
  · exact h
  · have : GeneralLinearGroup.map ((starRingEnd ℂ).comp (Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ))) y =
        GeneralLinearGroup.map (starRingEnd ℂ) (evGL (InfinitePlace.mk τ) y) := by
      ext i j
      rfl
    rw [this, h, map_one]

theorem evGL_cInf_of_mem {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) {w : InfinitePlace E}
    (h : w ≠ InfinitePlace.mk τ) : evGL w (cInf x) = 1 := by
  have h1 : x ∈ (cEmb (n := n) w.embedding).ker :=
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 w.embedding) (by rwa [InfinitePlace.mk_embedding])
  have h2 : GeneralLinearGroup.map (coord w.embedding) (cInf x) = 1 := MonoidHom.mem_ker.1 h1
  rwa [coord_embedding] at h2

def cutGA (τ : E →+* ℂ) : UA E n →* GA E n := (infGL E n).comp ((cutGL (InfinitePlace.mk τ)).comp cInf)

theorem cutGA_mem_UA (τ : E →+* ℂ) (g : UA E n) : cutGA τ g ∈ UA E n := by
  refine infGL_mem_UA (cutGL (InfinitePlace.mk τ) (cInf g)) ((unitary_iff_evGL _).2 fun w => ?_)
  by_cases h : w = InfinitePlace.mk τ
  · subst h
    rw [evGL_cutGL_self]
    exact (unitary_iff_evGL _).1 (cInf_unitary g) _
  · rw [evGL_cutGL_of_ne h]
    simp

theorem cInf_cutGA (τ : E →+* ℂ) (g : UA E n) :
    cInf (⟨cutGA τ g, cutGA_mem_UA τ g⟩ : UA E n) = cutGL (InfinitePlace.mk τ) (cInf g) :=
  pInf_infGL _

theorem cutGA_mem_embU (τ : E →+* ℂ) (g : UA E n) : (⟨cutGA τ g, cutGA_mem_UA τ g⟩ : UA E n) ∈ embU n τ := by
  refine ⟨pFin_infGL _, Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_⟩
  change GeneralLinearGroup.map (coord τ') (cInf _) = 1
  rw [cInf_cutGA]
  exact map_coord_of_evGL τ' (evGL_cutGL_of_ne h _)

def embRet (τ : E →+* ℂ) : UA E n →* embU n τ where
  toFun g := ⟨⟨cutGA τ g, cutGA_mem_UA τ g⟩, cutGA_mem_embU τ g⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (cutGA τ)))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul (cutGA τ) a b))

theorem cInf_embRet (τ : E →+* ℂ) (g : UA E n) :
    cInf (embRet τ g : UA E n) = cutGL (InfinitePlace.mk τ) (cInf g) := cInf_cutGA τ g

theorem continuous_embRet (τ : E →+* ℂ) : Continuous (embRet (n := n) τ) :=
  Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_infGL.comp ((continuous_cutGL _).comp continuous_cInf)) _) _

theorem embRet_apply (τ : E →+* ℂ) (x : embU n τ) : embRet τ (x : UA E n) = x := by
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · refine (cInf_embRet τ x.1).trans (gl_ext_evGL fun w => ?_)
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      exact evGL_cutGL_self _ _
    · rw [evGL_cutGL_of_ne h]
      exact (evGL_cInf_of_mem x.2 h).symm
  · exact (pFin_infGL _).trans (MonoidHom.mem_ker.1 x.2.1).symm

theorem commute_embRet (τ : E →+* ℂ) (g : UA E n) (y : embU n τ) :
    Commute ((embRet τ g : UA E n)⁻¹ * g) (y : UA E n) := by
  have h2 : GeneralLinearGroup.map (pFin E) y.1.1 = 1 := y.2.1
  have h1 : evGL (InfinitePlace.mk τ) (cInf ((embRet τ g : UA E n)⁻¹ * g)) = 1 := by
    rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, evGL_cutGL_self, inv_mul_cancel]
  generalize (embRet τ g : UA E n)⁻¹ * g = a at h1 ⊢
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * y.1) = cInf (y.1 * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      rw [h1, one_mul, mul_one]
    · rw [evGL_cInf_of_mem y.2 h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]

theorem exists_embRet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ),
    ∃ r : UA E n →* embU n τ, Continuous r ∧ (∀ x : embU n τ, r x = x) ∧
      ∀ (g : UA E n) (y : embU n τ), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) :=
  fun _ _ _ _ _ τ => ⟨embRet τ, continuous_embRet τ, embRet_apply τ, commute_embRet τ⟩

end GlobalTheory.DefU

end
