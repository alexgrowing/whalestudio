import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

open Classical in

def twist (τ : E →+* ℂ) : ℂ →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then RingHom.id ℂ else starRingEnd ℂ

theorem twist_twist (τ : E →+* ℂ) (z : ℂ) : twist τ (twist τ z) = z := by
  unfold twist; split_ifs <;> simp

theorem twist_star (τ : E →+* ℂ) (z : ℂ) : twist τ (star z) = star (twist τ z) := by
  unfold twist; split_ifs <;> simp

theorem continuous_twist (τ : E →+* ℂ) : Continuous (twist τ) := by
  unfold twist; split_ifs
  · exact continuous_id
  · exact Complex.continuous_conj

theorem twist_embedding (w : InfinitePlace E) : twist w.embedding = RingHom.id ℂ := by
  unfold twist; rw [if_pos (by rw [InfinitePlace.mk_embedding])]

theorem coord_eq (τ : E →+* ℂ) (z : Cinf E) : coord τ z = twist τ (z (InfinitePlace.mk τ)) := by
  unfold coord twist; split_ifs <;> rfl

open Classical in
theorem atEmb_apply (τ : E →+* ℂ) (z : ℂ) (w : InfinitePlace E) :
    atEmb τ z w = if w = InfinitePlace.mk τ then twist τ z else 0 := by
  unfold atEmb twist
  rw [Pi.single_apply]
  split_ifs <;> simp_all

def sN (τ : E →+* ℂ) : ℂ →ₙ+* Cinf E where
  toFun := atEmb τ
  map_mul' z z' := (atEmb_mul τ z z').symm
  map_zero' := funext fun w => by classical simp [atEmb_apply]
  map_add' z z' := funext fun w => by
    classical
    simp only [atEmb_apply, Pi.add_apply]
    split_ifs <;> simp

theorem sN_apply (τ : E →+* ℂ) (z : ℂ) : sN τ z = atEmb τ z := rfl

theorem continuous_sN (τ : E →+* ℂ) : Continuous (sN τ) := by
  classical
  refine continuous_pi fun w => ?_
  simp only [sN_apply, atEmb_apply]
  split_ifs
  · exact continuous_twist τ
  · exact continuous_const

def yG (τ : E →+* ℂ) : GL (Fin n) ℂ →* GL (Fin n) (Cinf E) := cornerGL n (sN τ)

open Classical in
theorem yG_apply (τ : E →+* ℂ) (g : GL (Fin n) ℂ) (i j : Fin n) (w : InfinitePlace E) :
    (yG τ g).val i j w =
      if w = InfinitePlace.mk τ then twist τ (g.val i j) else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  change (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j w - sN τ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) w +
    sN τ (g.val i j) w = _
  simp only [sN_apply, atEmb_apply, Matrix.one_apply]
  split_ifs <;> simp_all

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cEmb_mem (τ : E →+* ℂ) (x : UA E n) : (cEmb τ x).val ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 := congrArg (RingHom.mapMatrix ((coord τ).comp (pInf E))) hx
  rw [mul_one, map_mul, map_one] at h1
  rw [Matrix.mem_unitaryGroup_iff', ← h1]
  congr 1
  ext i j
  exact (GlobalTheory.DefiniteBC.coord_conjAd τ _).symm

theorem cEmb_infGL (τ' : E →+* ℂ) (y : GL (Fin n) (Cinf E)) (h : infGL E n y ∈ UA E n) (i j : Fin n) :
    (cEmb τ' ⟨_, h⟩).val i j = coord τ' (y.val i j) := by
  have e : cEmb τ' ⟨_, h⟩ = GeneralLinearGroup.map (coord τ') y := by
    change GeneralLinearGroup.map (coord τ') (GeneralLinearGroup.map (pInf E) (infGL E n y)) = _
    rw [pInf_infGL]
  rw [e]
  rfl

theorem yG_unitary (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (yG τ (GlobalTheory.Branching.unitaryIncl n u)).valᴴ * (yG τ (GlobalTheory.Branching.unitaryIncl n u)).val = 1 := by
  classical
  have hu : star (u : Matrix (Fin n) (Fin n) ℂ) * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
  refine Matrix.ext fun i j => funext fun w => ?_
  simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply, yG_apply]
  split_ifs with hw
  · have h2 := congrFun₂ hu i j
    simp only [Matrix.mul_apply, Matrix.star_apply] at h2
    simp only [← twist_star, ← map_mul, ← map_sum]
    change twist τ (∑ k, star ((u : Matrix (Fin n) (Fin n) ℂ) k i) * (u : Matrix (Fin n) (Fin n) ℂ) k j) = _
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · by_cases h : i = j
    · subst h; simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h, Ne.symm h]

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem infGL_yG_mem_UA (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)) ∈ UA E n :=
  infGL_mem_UA _ (yG_unitary τ u)

theorem twist_one_apply (τ : E →+* ℂ) (i j : Fin n) :
    twist τ ((1 : Matrix (Fin n) (Fin n) ℂ) i j) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem mem_embU (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) :
    (⟨_, infGL_yG_mem_UA τ u⟩ : UA E n) ∈ embU n τ := by
  classical
  refine ⟨pFin_infGL _, ?_⟩
  refine Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [cEmb_infGL, coord_eq, yG_apply, if_neg h, twist_one_apply]
  rfl

def inv (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) : embU n τ :=
  ⟨⟨_, infGL_yG_mem_UA τ u⟩, mem_embU τ u⟩

def fwd (τ : E →+* ℂ) (x : embU n τ) : Matrix.unitaryGroup (Fin n) ℂ := ⟨(cEmb τ x.1).val, cEmb_mem τ x.1⟩

theorem fwd_inv (τ : E →+* ℂ) (u : Matrix.unitaryGroup (Fin n) ℂ) : fwd τ (inv τ u) = u := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change (cEmb τ ⟨_, infGL_yG_mem_UA τ u⟩).val i j = _
  rw [cEmb_infGL, coord_eq, yG_apply, if_pos rfl, twist_twist]
  rfl

theorem inv_fwd (τ : E →+* ℂ) (x : embU n τ) : inv τ (fwd τ x) = x := by
  classical
  have hx := Subgroup.mem_inf.1 x.2
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · change GeneralLinearGroup.map (pInf E) (infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n (fwd τ x)))) = _
    rw [pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
    rw [yG_apply]
    split_ifs with hw
    · subst hw
      change twist τ (coord τ (pInf E (x.1.1.val i j))) = _
      rw [coord_eq, twist_twist]
      rfl
    · have h1 : InfinitePlace.mk w.embedding ≠ InfinitePlace.mk τ := by
        rw [InfinitePlace.mk_embedding]; exact hw
      have hk := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 w.embedding) h1)
      have h2 := congrArg (fun g : GL (Fin n) ℂ => g.val i j) hk
      change coord w.embedding (pInf E (x.1.1.val i j)) = _ at h2
      rw [coord_eq, twist_embedding, InfinitePlace.mk_embedding] at h2
      exact h2.symm
  · change GeneralLinearGroup.map (pFin E) (infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n (fwd τ x)))) = _
    rw [pFin_infGL]
    exact (MonoidHom.mem_ker.1 hx.1).symm

end GlobalTheory.EmbUnitary

namespace GlobalTheory.EmbUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  have : (coord τ : Cinf E → ℂ) = fun z => twist τ (z (InfinitePlace.mk τ)) := funext (coord_eq τ)
  rw [this]
  exact (continuous_twist τ).comp (continuous_apply _)

theorem continuous_fwd (τ : E →+* ℂ) : Continuous (fwd τ : embU n τ → Matrix.unitaryGroup (Fin n) ℂ) := by
  refine Continuous.subtype_mk ?_ _
  change Continuous fun x : embU n τ => (x.1.1.val).map (fun a => coord τ (pInf E a))
  exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_map
    ((continuous_coord τ).comp continuous_pInf')

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

def phi (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (Ad E) :=
  corner (matN n (sInf E)) (corner (matN n (sN τ)) M)

theorem continuous_phi (τ : E →+* ℂ) : Continuous (phi (n := n) τ) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) ℂ => 1 - matN n (sInf E) 1 +
    (1 - matN n (sN τ) 1 + M.map (sN τ)).map (sInf E)
  exact continuous_const.add ((continuous_const.add (continuous_id.matrix_map (continuous_sN τ))).matrix_map
    continuous_sInf)

theorem continuous_inv (τ : E →+* ℂ) : Continuous (inv τ : Matrix.unitaryGroup (Fin n) ℂ → embU n τ) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ => phi τ (u : Matrix (Fin n) (Fin n) ℂ)
    exact (continuous_phi τ).comp continuous_subtype_val
  · have e : ∀ u : Matrix.unitaryGroup (Fin n) ℂ,
        ((infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)))⁻¹ : GL (Fin n) (Ad E)).val =
          phi τ (star (u : Matrix (Fin n) (Fin n) ℂ)) := fun u => by
      rw [← map_inv, ← map_inv]
      rfl
    change Continuous fun u : Matrix.unitaryGroup (Fin n) ℂ =>
      ((infGL E n (yG τ (GlobalTheory.Branching.unitaryIncl n u)))⁻¹ : GL (Fin n) (Ad E)).val
    simp only [e]
    exact (continuous_phi τ).comp (continuous_star.comp continuous_subtype_val)

def equiv (τ : E →+* ℂ) : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ where
  toFun := fwd τ
  invFun := inv τ
  left_inv := inv_fwd τ
  right_inv := fwd_inv τ
  map_mul' x y := Subtype.ext (by
    change (cEmb τ (x.1 * y.1)).val = (cEmb τ x.1).val * (cEmb τ y.1).val
    rw [map_mul]
    rfl)
  continuous_toFun := continuous_fwd τ
  continuous_invFun := continuous_inv τ

theorem exists_equiv_unitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ),
    ∃ e : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ, ∀ x : embU n τ,
      GlobalTheory.Branching.unitaryIncl n (e x) = cEmb τ (x : UA E n) := by
  intro E _ _ _ n τ
  exact ⟨equiv τ, fun x => Units.ext rfl⟩

end GlobalTheory.EmbUnitary
