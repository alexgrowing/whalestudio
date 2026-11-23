import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDifferentPair

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

abbrev Lz (E : Type) [Field E] (m : ℕ) : Type := Submodule (𝓞 E) (Fin m → E) × (Fin m → E)

def zOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => P i (Fin.last r)

def spanX {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (eOf P).mulVecLin

def perpX (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule E (Fin n → E) := LinearMap.ker (cT σ (eOf P) * J).mulVecLin

def latIn {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (S : Submodule E (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ ⊓ S.restrictScalars (𝓞 E)

def mulLat {n : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map ((g : 𝓞 E) • LinearMap.id)

def IsRed (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) (x : Lz E m)
    (al : Matrix (Fin m) (Fin n) E) : Prop :=
  (∀ v ∈ perpX σ J P, al *ᵥ v = 0 ↔ v ∈ spanX P) ∧
  (∀ y, ∃ v ∈ perpX σ J P, al *ᵥ v = y) ∧
  (∀ v ∈ perpX σ J P, ∀ w ∈ perpX σ J P, form σ Jb (al *ᵥ v) (al *ᵥ w) = form σ J v w) ∧
  (latIn Λ (perpX σ J P)).map (al.mulVecLin.restrictScalars (𝓞 E)) = x.1 ∧
  al *ᵥ zOf P = x.2

def ModIso (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (g : ℕ)
    (L' L : Submodule (𝓞 E) (Fin m → E)) (Γ : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) : Prop :=
  Γ ≤ L'.prod L ∧ (mulLat g L').prod (mulLat g L) ≤ Γ ∧
  (∀ y' ∈ L', ∃ y, (y', y) ∈ Γ) ∧ (∀ y ∈ L, ∃ y', (y', y) ∈ Γ) ∧
  (∀ y, ((0 : Fin m → E), y) ∈ Γ → y ∈ mulLat g L) ∧
  (∀ y', (y', (0 : Fin m → E)) ∈ Γ → y' ∈ mulLat g L') ∧
  ∀ p ∈ Γ, ∀ q ∈ Γ, ∃ t : 𝓞 E, form σ Jb p.1 q.1 - form σ Jb p.2 q.2 = (g : E) * algebraMap (𝓞 E) E t

def iotaOf (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E)
    (al al' : Matrix (Fin m) (Fin n) E) : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E)) :=
  ((latIn Λ (perpX σ J P')).prod (latIn Λ (perpX σ J P)) ⊓
      (mulLat g Λ ⊔ latIn Λ (spanX P)).comap (LinearMap.snd (𝓞 E) _ _ - LinearMap.fst (𝓞 E) _ _)).map
    ((al'.mulVecLin.restrictScalars (𝓞 E)).prodMap (al.mulVecLin.restrictScalars (𝓞 E)))

def IsRow (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (g : ℕ) (x x' : Lz E m)
    (Γ : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) : Prop :=
  ModIso σ Jb g x'.1 x.1 Γ ∧ (x'.2, x.2) ∈ Γ

def LzClass (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (T : E) : Type :=
  Quot fun x y : LzSet σ Jb T => ∃ γ, IsoLz σ Jb γ x.1 y.1

def lzRep {σ : E →+* E} {m : ℕ} {Jb : Matrix (Fin m) (Fin m) E} {T : E} (c : LzClass σ Jb T) : Lz E m :=
  (Quot.out c).1

def Rows (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (T T' : E) (g : ℕ) :
    Set (LzClass σ Jb T × LzClass σ Jb T' × Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) :=
  {ρ | IsRow σ Jb g (lzRep ρ.1) (lzRep ρ.2.1) ρ.2.2}

def autLz (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (x : Lz E m) : ℕ∞ :=
  ENat.card {γ : Matrix (Fin m) (Fin m) E // IsoLz σ Jb γ x x}

def wt (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (x x' : Lz E m) : ENNReal :=
  (ENat.toENNReal (autLz σ Jb x) * ENat.toENNReal (autLz σ Jb x'))⁻¹

abbrev Rig (E : Type) [Field E] [NumberField E] (n m r : ℕ) : Type :=
  Tri E n r × Matrix (Fin m) (Fin n) E × Matrix (Fin m) (Fin n) E

def RigConf (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (T T' : E) (g : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (x x' : Lz E m)
    (Γ : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) : Set (Rig E n m r) :=
  {c | c.1 ∈ GenConf σ J T T' g Z ∧ IsRed σ J Jb c.1.1 c.1.2.1 x c.2.1 ∧
    IsRed σ J Jb c.1.1 c.1.2.2 x' c.2.2 ∧ iotaOf σ J g c.1.1 c.1.2.1 c.1.2.2 c.2.1 c.2.2 = Γ}

def IsoRig (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : Matrix (Fin n) (Fin n) E)
    (c d : Rig E n m r) : Prop :=
  IsoTri σ J γ c.1 d.1 ∧ (∀ v ∈ perpX σ J c.1.2.1, d.2.1 *ᵥ (γ *ᵥ v) = c.2.1 *ᵥ v) ∧
    ∀ v ∈ perpX σ J c.1.2.2, d.2.2 *ᵥ (γ *ᵥ v) = c.2.2 *ᵥ v

def rigCount (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (T T' : E) (g : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (x x' : Lz E m)
    (Γ : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) : ℕ∞ :=
  ENat.card (Quot fun c d : RigConf σ J Jb T T' g Z x x' Γ => ∃ γ, IsoRig σ J γ c.1 d.1)

def rigSum (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (T T' : E) (g : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ENNReal :=
  ∑' ρ : Rows σ Jb T T' g, wt σ Jb (lzRep ρ.1.1) (lzRep ρ.1.2.1) *
    ENat.toENNReal (rigCount σ J Jb T T' g Z (lzRep ρ.1.1) (lzRep ρ.1.2.1) ρ.1.2.2)

def UO (E : Type) [Field E] [NumberField E] (r : ℕ) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {u | IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)}

def congruencePairs (E : Type) [Field E] [NumberField E] (r g : ℕ) :
    Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E × Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {p | p.1 ∈ UO E r ∧ p.2 ∈ UO E r ∧
    ∀ a b : Fin (r + 1), a < b → ∃ t ∈ dInv E ((b : ℕ) - a), p.1 a b - p.2 a b = (g : E) * t}

section Basic

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

omit [NumberField E] in

theorem mem_spanX (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ spanX P ↔ ∃ c, eOf P *ᵥ c = v := Iff.rfl

omit [NumberField E] in

theorem mem_perpX (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ (cT σ (eOf P) * J) *ᵥ v = 0 := Iff.rfl

omit [NumberField E] in

theorem mem_perpX_iff_form (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ ∀ a : Fin r, form σ J v (fun i => P i a.castSucc) = 0 := by
  rw [mem_perpX, ← Matrix.mulVec_mulVec, funext_iff]
  rfl

omit [NumberField E] in

theorem mem_mulLat (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ mulLat g Λ ↔ ∃ w ∈ Λ, (g : E) • w = v := by
  simp only [mulLat, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply,
    Nat.cast_smul_eq_nsmul]

omit [NumberField E] in

theorem mulLat_le (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) : mulLat g Λ ≤ Λ := by
  rintro _ ⟨w, hw, rfl⟩
  exact Λ.smul_mem _ hw

omit [NumberField E] in

theorem mem_latMap (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ latMap γ Λ ↔ ∃ w ∈ Λ, γ *ᵥ w = v := Iff.rfl

omit [NumberField E] in

theorem IsRed.mem_iff {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E} {x : Lz E m}
    {al : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (y : Fin m → E) :
    y ∈ x.1 ↔ ∃ v ∈ latIn Λ (perpX σ J P), al *ᵥ v = y := by
  rw [← h.2.2.2.1]
  rfl

omit [NumberField E] in

theorem col_mem_perpX {T : E} {P : Matrix (Fin n) (Fin (r + 1)) E} (h : IsFrame σ J T P)
    (b : Fin (r + 1)) : (fun i => P i b) ∈ perpX σ J P := by
  rw [mem_perpX_iff_form]
  intro a
  have h1 := congrFun (congrFun h.2 a.castSucc) b
  rw [pairM, Matrix.mul_assoc] at h1
  refine h1.trans ?_
  simp [TF, Matrix.diagonal_apply, (Fin.castSucc_lt_last a).ne]

omit [NumberField E] in

theorem zOf_mem_perpX {T : E} {P : Matrix (Fin n) (Fin (r + 1)) E} (h : IsFrame σ J T P) :
    zOf P ∈ perpX σ J P := col_mem_perpX h _

omit [NumberField E] in

theorem IsRed.congr {T : E} {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {x : Lz E m} {al bl : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (hP : IsFrame σ J T P)
    (hb : ∀ v ∈ perpX σ J P, bl *ᵥ v = al *ᵥ v) : IsRed σ J Jb Λ P x bl := by
  refine ⟨fun v hv => by rw [hb v hv, h.1 v hv], fun y => ?_,
    fun v hv w hw => by rw [hb v hv, hb w hw, h.2.2.1 v hv w hw], ?_,
    (hb _ (zOf_mem_perpX hP)).trans h.2.2.2.2⟩
  · obtain ⟨v, hv, rfl⟩ := h.2.1 y
    exact ⟨v, hv, hb v hv⟩
  · ext y
    rw [h.mem_iff]
    exact ⟨fun ⟨v, hv, e⟩ => ⟨v, hv, (hb v hv.2).symm.trans e⟩,
      fun ⟨v, hv, e⟩ => ⟨v, hv, (hb v hv.2).trans e⟩⟩

omit [NumberField E] in

theorem form_mulVec {γ : Matrix (Fin n) (Fin n) E} (h : IsUn σ J γ) (v w : Fin n → E) :
    form σ J (γ *ᵥ v) (γ *ᵥ w) = form σ J v w := by
  have e : (fun i => σ ((γ *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* cT σ γ := by
    ext i
    simp [cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [form, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, form]

omit [NumberField E] in

theorem isUnit_det_of_isUn {γ : Matrix (Fin n) (Fin n) E} (hJ : IsUnit J.det) (h : IsUn σ J γ) :
    IsUnit γ.det := by
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul] at e
  exact isUnit_of_mul_isUnit_right (e ▸ hJ)

omit [NumberField E] in

theorem mulVec_mem_perpX {γ : Matrix (Fin n) (Fin n) E} (h : IsUn σ J γ)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    γ *ᵥ v ∈ perpX σ J (γ * P) ↔ v ∈ perpX σ J P := by
  simp only [mem_perpX_iff_form]
  refine forall_congr' fun a => ?_
  rw [← form_mulVec h v]
  rfl

omit [NumberField E] in

theorem IsRed.comp {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E} {x y : Lz E m}
    {al : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (hJ : IsUnit Jb.det)
    {γ : Matrix (Fin m) (Fin m) E} (hγ : IsoLz σ Jb γ x y) : IsRed σ J Jb Λ P y (γ * al) := by
  have hu : IsUnit γ := (Matrix.isUnit_iff_isUnit_det γ).2 (isUnit_det_of_isUn hJ hγ.1)
  refine ⟨fun v hv => ?_, fun w => ?_, fun v hv w hw => ?_, ?_, ?_⟩
  · rw [← h.1 v hv, ← Matrix.mulVec_mulVec]
    exact ⟨fun e => Matrix.mulVec_injective_iff_isUnit.2 hu (e.trans (Matrix.mulVec_zero γ).symm),
      fun e => by rw [e, Matrix.mulVec_zero]⟩
  · obtain ⟨w', rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu w
    obtain ⟨v, hv, rfl⟩ := h.2.1 w'
    exact ⟨v, hv, (Matrix.mulVec_mulVec _ _ _).symm⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, form_mulVec hγ.1, h.2.2.1 v hv w hw]
  · rw [← hγ.2.1, ← h.2.2.2.1, latMap, ← Submodule.map_comp, Matrix.mulVecLin_mul]
    rfl
  · rw [← Matrix.mulVec_mulVec, h.2.2.2.2, hγ.2.2]

end Basic

section Iota

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

end Iota

section Iso

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

omit [NumberField E] in

theorem isUn_one : IsUn σ J 1 := by
  simp [IsUn, cT, Matrix.map_one]

omit [NumberField E] in

theorem isUn_mul {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (hδ : IsUn σ J δ) :
    IsUn σ J (γ * δ) := by
  have e : cT σ (γ * δ) = cT σ δ * cT σ γ := by rw [cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  rw [IsUn, e, show cT σ δ * cT σ γ * J * (γ * δ) = cT σ δ * (cT σ γ * J * γ) * δ by
    simp only [Matrix.mul_assoc], hγ, hδ]

omit [NumberField E] in

theorem isUn_of_mul_eq_one {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (h : γ * δ = 1) :
    IsUn σ J δ := by
  have e : cT σ δ * cT σ γ = 1 := by
    rw [cT, cT, ← Matrix.transpose_mul, ← Matrix.map_mul, h]
    simp [Matrix.map_one]
  rw [IsUn, ← hγ, show cT σ δ * (cT σ γ * J * γ) * δ = cT σ δ * cT σ γ * J * (γ * δ) by
    simp only [Matrix.mul_assoc], e, h, Matrix.one_mul, Matrix.mul_one, hγ]

theorem latMap_one (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext v
  simp [mem_latMap]

theorem latMap_mul (γ δ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    latMap (γ * δ) Λ = latMap γ (latMap δ Λ) := by
  rw [latMap, latMap, latMap, ← Submodule.map_comp, Matrix.mulVecLin_mul]
  rfl

theorem IsoRig.mul {γ δ : Matrix (Fin n) (Fin n) E} {c d e : Rig E n m r} (h : IsoRig σ J γ c d)
    (k : IsoRig σ J δ d e) : IsoRig σ J (δ * γ) c e := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
  obtain ⟨⟨k1, k2, k3, k4⟩, k5, k6⟩ := k
  refine ⟨⟨isUn_mul k1 h1, by rw [latMap_mul, h2, k2], by rw [Matrix.mul_assoc, h3, k3],
    by rw [Matrix.mul_assoc, h4, k4]⟩, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← Matrix.mulVec_mulVec, k5 _ (h3 ▸ (mulVec_mem_perpX h1 _ v).2 hv), h5 v hv]
  · rw [← Matrix.mulVec_mulVec, k6 _ (h4 ▸ (mulVec_mem_perpX h1 _ v).2 hv), h6 v hv]

theorem IsoRig.inv (hJ : IsUnit J.det) {γ : Matrix (Fin n) (Fin n) E} {c d : Rig E n m r}
    (h : IsoRig σ J γ c d) : IsoRig σ J γ⁻¹ d c := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := h
  have hu := isUnit_det_of_isUn hJ h1
  have l := Matrix.nonsing_inv_mul γ hu
  have s := Matrix.mul_nonsing_inv γ hu
  have e (v : Fin n → E) : γ *ᵥ (γ⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, s, Matrix.one_mulVec]
  refine ⟨⟨isUn_of_mul_eq_one h1 s, by rw [← h2, ← latMap_mul, l, latMap_one],
    by rw [← h3, ← Matrix.mul_assoc, l, Matrix.one_mul],
    by rw [← h4, ← Matrix.mul_assoc, l, Matrix.one_mul]⟩, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← h5 _ ((mulVec_mem_perpX h1 _ _).1 (by rwa [e, h3])), e]
  · rw [← h6 _ ((mulVec_mem_perpX h1 _ _).1 (by rwa [e, h4])), e]

theorem IsRed.transport (hJ : IsUnit J.det) {T : E} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {P : Matrix (Fin n) (Fin (r + 1)) E} {x : Lz E m} {al bl : Matrix (Fin m) (Fin n) E}
    (h : IsRed σ J Jb Λ P x al) (hP : IsFrame σ J T P) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ)
    (hb : ∀ v ∈ perpX σ J P, bl *ᵥ (γ *ᵥ v) = al *ᵥ v) : IsRed σ J Jb (latMap γ Λ) (γ * P) x bl := by
  have hu : IsUnit γ := (Matrix.isUnit_iff_isUnit_det γ).2 (isUnit_det_of_isUn hJ hγ)
  have hs := Matrix.mulVec_surjective_iff_isUnit.2 hu
  have he : eOf (γ * P) = γ * eOf P := rfl
  refine ⟨fun v hv => ?_, fun y => ?_, fun v hv w hw => ?_, ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := hs v
    rw [mulVec_mem_perpX hγ] at hv
    rw [hb v hv, h.1 v hv, mem_spanX, mem_spanX, he]
    refine exists_congr fun c => ?_
    rw [← Matrix.mulVec_mulVec]
    exact (Matrix.mulVec_injective_iff_isUnit.2 hu).eq_iff.symm
  · obtain ⟨v, hv, rfl⟩ := h.2.1 y
    exact ⟨_, (mulVec_mem_perpX hγ P v).2 hv, hb v hv⟩
  · obtain ⟨v, rfl⟩ := hs v
    obtain ⟨w, rfl⟩ := hs w
    rw [mulVec_mem_perpX hγ] at hv hw
    rw [hb v hv, hb w hw, h.2.2.1 v hv w hw, form_mulVec hγ]
  · ext y
    rw [h.mem_iff]
    constructor
    · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hv'⟩, rfl⟩
      have hv'' := (mulVec_mem_perpX hγ P v).1 hv'
      exact ⟨v, ⟨hv, hv''⟩, (hb v hv'').symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨γ *ᵥ v, ⟨⟨v, hv.1, rfl⟩, (mulVec_mem_perpX hγ P v).2 hv.2⟩, hb v hv.2⟩
  · exact (hb _ (zOf_mem_perpX hP)).trans h.2.2.2.2

end Iso

section Unip

variable {n r : ℕ}

theorem mul_mem_dInv {i j : ℕ} {a b : E} (ha : a ∈ dInv E i) (hb : b ∈ dInv E j) :
    a * b ∈ dInv E (i + j) := by
  rw [dInv, pow_add]
  exact FractionalIdeal.mul_mem_mul ha hb

theorem UO.entry_mem {u : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hu : u ∈ UO E r) (a b : Fin (r + 1)) :
    u a b ∈ dInv E ((b : ℕ) - a) := by
  rcases lt_trichotomy a b with h | rfl | h
  · exact hu.2 a b h
  · rw [(hu.1 a a).2 rfl, Nat.sub_self, dInv, pow_zero]
    exact FractionalIdeal.one_mem_one _
  · rw [(hu.1 a b).1 h]
    exact FractionalIdeal.zero_mem _

theorem one_mem_UO : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) ∈ UO E r :=
  ⟨fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩,
    fun _ _ h => by rw [Matrix.one_apply_ne h.ne]; exact FractionalIdeal.zero_mem _⟩

theorem frameLat_mul_le (P : Matrix (Fin n) (Fin (r + 1)) E) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hu : u ∈ UO E r) : frameLat (P * u) ≤ frameLat P := by
  rw [frameLat, Submodule.span_le]
  rintro _ ⟨b, c, hc, rfl⟩
  have e : (c • fun i => (P * u) i b) = ∑ a, (c * u a b) • fun i => P i a := by
    ext i
    simp only [Matrix.mul_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  refine Submodule.sum_mem _ fun a _ => ?_
  rcases lt_or_ge b a with h | h
  · rw [(hu.1 a b).1 h, mul_zero, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.subset_span ⟨a, _, ?_, rfl⟩
    have h1 : (a : ℕ) ≤ b := h
    have h2 := b.2
    rw [show r - (a : ℕ) = r - (b : ℕ) + ((b : ℕ) - a) by omega]
    exact mul_mem_dInv hc (UO.entry_mem hu a b)

end Unip

section Examples

variable {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

example (σ : E →+* E) (Λ : Submodule (𝓞 E) (Fin 3 → E)) :
    ∃ L, IsRed (r := 1) σ !![0, 1, 0; 1, 0, 0; 0, 0, -1] !![-1] Λ !![1, 0; 0, 0; 0, 1] (L, ![1])
      !![0, 0, 1] := by
  have hp (v : Fin 3 → E) : v ∈ perpX (r := 1) σ !![0, 1, 0; 1, 0, 0; 0, 0, -1] !![1, 0; 0, 0; 0, 1] ↔
      v 1 = 0 := by
    simp [mem_perpX_iff_form, form, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  refine ⟨_, fun v hv => ?_, fun y => ⟨![0, 0, y 0], (hp _).2 rfl, ?_⟩, fun v hv w hw => ?_, rfl, ?_⟩
  · rw [hp] at hv
    constructor
    · intro h
      have h2 : v 2 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 0
      refine ⟨![v 0], ?_⟩
      ext i
      fin_cases i <;> simp [eOf, Matrix.mulVec, dotProduct, hv, h2]
    · rintro ⟨c, rfl⟩
      ext i
      fin_cases i
      simp [eOf, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · rw [hp] at hv hw
    simp [form, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv, hw]
  · ext i
    fin_cases i
    simp [zOf, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

example (t : E) : (!![1, t; 0, 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) E) ∈ UO E 1 ↔ t ∈ dInv E 1 := by
  refine ⟨fun h => h.2 0 1 (by decide), fun h => ⟨fun i j => ?_, fun a b hab => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp
  · fin_cases a <;> fin_cases b <;> first | exact h | exact absurd hab (by decide)

end Examples

end GlobalTheory.SgGlob
