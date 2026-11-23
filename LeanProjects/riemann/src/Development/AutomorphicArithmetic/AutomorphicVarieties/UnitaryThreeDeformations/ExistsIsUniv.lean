import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriCanon
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivEx

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

section
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private def Cut (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    (P : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop) : Prop :=
  ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'),
    P R' f ↔ ∀ x ∈ I, f x = 0

omit [IsCO O R] in
private theorem Cut.eq (x y : R) : Cut O R fun _ _ _ _ f => f x = f y := by
  refine ⟨Ideal.span {x - y}, fun R' _ _ _ f => ?_⟩
  beta_reduce
  constructor
  · intro h z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, map_sub, h, sub_self, mul_zero]
  · intro h
    have hxy := h (x - y) (Ideal.subset_span rfl)
    rwa [map_sub, sub_eq_zero] at hxy

omit [IsCO O R] in
private theorem Cut.all {κ : Sort*} {P : κ → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : ∀ i, Cut O R (P i)) : Cut O R fun R' _ _ _ f => ∀ i, P i R' f := by
  choose I hI using h
  refine ⟨⨆ i, I i, fun R' _ _ _ f => ?_⟩
  beta_reduce
  constructor
  · intro H z hz
    have hle : ⨆ i, I i ≤ RingHom.ker (f : R →+* R') :=
      iSup_le fun i y hy => (hI i R' f).mp (H i) y hy
    exact hle hz
  · intro H i
    exact (hI i R' f).mpr fun z hz => H z (Ideal.mem_iSup_of_mem i hz)

omit [IsCO O R] in
private theorem Cut.and {P Q : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : Cut O R P) (h' : Cut O R Q) : Cut O R fun R' _ _ _ f => P R' f ∧ Q R' f := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨J, hJ⟩ := h'
  refine ⟨I ⊔ J, fun R' _ _ _ f => ?_⟩
  beta_reduce
  rw [hI R' f, hJ R' f]
  constructor
  · rintro ⟨h1, h2⟩ z hz
    have hle : I ⊔ J ≤ RingHom.ker (f : R →+* R') := sup_le (fun y hy => h1 y hy) (fun y hy => h2 y hy)
    exact hle hz
  · intro H
    exact ⟨fun z hz => H z (Ideal.mem_sup_left hz), fun z hz => H z (Ideal.mem_sup_right hz)⟩

omit [IsCO O R] in
private theorem Cut.congr {P Q : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : Cut O R P) (e : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), Q R' f ↔ P R' f) :
    Cut O R Q := by
  obtain ⟨I, hI⟩ := h
  exact ⟨I, fun R' _ _ _ f => (e R' f).trans (hI R' f)⟩

private theorem locHom {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') :
    IsLocalHom (f : R →+* R') := by
  constructor
  intro x hx
  by_contra hnu
  have hm : x ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).mpr hnu
  have h0 : res O R' (f x) = 0 := by
    rw [res_map, res_eq_zero_iff]
    exact hm
  rw [res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
  exact h0 hx

private theorem map_max {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R}
    (hx : x ∈ maximalIdeal R) : f x ∈ maximalIdeal R' := by
  rwa [← res_eq_zero_iff O, res_map f, res_eq_zero_iff]

private theorem red_push {D : Type} [Group D] {η : D →* ℤˣ} {Ψ : D →* Oˣ} {r : D →* GG 3 R} (hr : Red η Ψ r)
    {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') : Red η Ψ (UnitaryThreeInertia.push f r) where
  mult g := hr.mult g
  red g a b := by
    have := map_max f (hr.red g a b)
    simpa using this

private theorem cont_push {D : Type} [Group D] [TopologicalSpace D] {r : D →* GG 3 R}
    (hr : UnitaryThreeInertia.AdicCont (maximalIdeal R) r)
    {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') :
    UnitaryThreeInertia.AdicCont (maximalIdeal R') (UnitaryThreeInertia.push f r) := by
  intro n
  have hle : maximalIdeal R ^ n ≤ (maximalIdeal R' ^ n).comap (f : R →+* R') := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono
      (Ideal.map_le_iff_le_comap.mpr fun y hy => Ideal.mem_comap.mpr (map_max f hy)) n
  have hq := (hr n).comp
    (fun M : Matrix (Fin 3) (Fin 3) (R ⧸ maximalIdeal R ^ n) => M.map (Ideal.quotientMap _ (f : R →+* R') hle))
  convert hq using 1
  funext g
  ext a b
  simp [UnitaryThreeInertia.push, GG.map_mat, Ideal.quotientMap_mk]

omit [IsCO O R] [IsLocalRing O] in
private theorem conj_push {D : Type} [Group D] (r : D →* GG 3 R) (h : GL (Fin 3) R)
    {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (g : D) (a b : Fin 3) :
    (conjBy (GeneralLinearGroup.map (f : R →+* R') h)⁻¹ (UnitaryThreeInertia.push f r) g).mat a b = f ((conjBy h⁻¹ r g).mat a b) := by
  have e : conjBy (GeneralLinearGroup.map (f : R →+* R') h)⁻¹ (UnitaryThreeInertia.push f r) g =
      GG.map (f : R →+* R') (conjBy h⁻¹ r g) := by
    simp only [conjBy, UnitaryThreeInertia.push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, inv_inv]
    simp [GG.map, SemidirectProduct.map_inl]
  rw [e, GG.map_mat]
  rfl

private theorem psi_unit {A : Type} [CommRing A] (t : Aˣ) (hu : IsUnit ((t : A) ^ 2 - 1)) (a b : Fin 3) (hab : a ≠ b) :
    IsUnit (((t ^ wt1 a : Aˣ) : A) - ((t ^ wt1 b : Aˣ) : A)) := by
  have hti : (t : A) * ((t⁻¹ : Aˣ) : A) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : A) - 1) := by
    have e : (t : A) ^ 2 - 1 = ((t : A) - 1) * ((t : A) + 1) := by ring
    rw [e] at hu
    exact isUnit_of_mul_isUnit_left hu
  have hiu : IsUnit ((t⁻¹ : Aˣ) : A) := Units.isUnit _
  fin_cases a <;> fin_cases b <;> simp at hab <;> simp [wt1]
  · exact h1
  · have e : (t : A) - ((t⁻¹ : Aˣ) : A) = ((t⁻¹ : Aˣ) : A) * ((t : A) ^ 2 - 1) := by
      linear_combination (-(t : A)) * hti
    rw [e]
    exact hiu.mul hu
  · have e : (1 : A) - (t : A) = -((t : A) - 1) := by ring
    rw [e]
    exact h1.neg
  · have e : (1 : A) - ((t⁻¹ : Aˣ) : A) = ((t⁻¹ : Aˣ) : A) * ((t : A) - 1) := by
      linear_combination -hti
    rw [e]
    exact hiu.mul h1
  · have e : ((t⁻¹ : Aˣ) : A) - (t : A) = -(((t⁻¹ : Aˣ) : A) * ((t : A) ^ 2 - 1)) := by
      linear_combination (t : A) * hti
    rw [e]
    exact (hiu.mul hu).neg
  · have e : ((t⁻¹ : Aˣ) : A) - 1 = -(((t⁻¹ : Aˣ) : A) * ((t : A) - 1)) := by
      linear_combination hti
    rw [e]
    exact (hiu.mul h1).neg

private theorem cut_TD {D : Type} [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R)
    (hr : Red η Ψ r) (x : D) (hx : η x = 1) (hu : IsUnit ((Ψ x : O) ^ 2 - 1)) :
    (Cut O R fun _ _ _ _ f => CondT η Ψ I (UnitaryThreeInertia.push f r)) ∧ Cut O R fun _ _ _ _ f => CondD η Ψ I (UnitaryThreeInertia.push f r) := by
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hr0 : (r0 η Ψ x).mat = diagonal fun i => ((Ψ x ^ wt1 i : Oˣ) : O) := tor_val (Ψ x)
  have hred : ∀ a b, (r x).mat a b - algebraMap O R ((r0 η Ψ x).mat a b) ∈ maximalIdeal R :=
    fun a b => hr.red x a b
  obtain ⟨h, hh⟩ : ∃ h, Canon (r x).mat h := by
    apply exists_canon
    · intro a b hab
      have hu' : IsUnit (algebraMap O R (((Ψ x ^ wt1 a : Oˣ) : O) - ((Ψ x ^ wt1 b : Oˣ) : O))) :=
        (psi_unit (Ψ x) hu a b hab).map _
      have hm : (r x).mat a a - (r x).mat b b -
          algebraMap O R (((Ψ x ^ wt1 a : Oˣ) : O) - ((Ψ x ^ wt1 b : Oˣ) : O)) ∈ maximalIdeal R := by
        have h1 := hred a a
        have h2 := hred b b
        rw [hr0, diagonal_apply_eq] at h1 h2
        have h3 := sub_mem h1 h2
        rw [map_sub]
        convert h3 using 1
        ring
      by_contra hn
      have hmem : (r x).mat a a - (r x).mat b b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hn
      have h4 := sub_mem hmem hm
      rw [sub_sub_cancel] at h4
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h4) hu'
    · intro a b hab
      have h1 := hred a b
      rw [hr0, diagonal_apply_ne _ hab, map_zero, sub_zero] at h1
      exact h1
  have CT := Cut.and
    (Cut.all fun g => Cut.all fun _ : g ∈ η.ker => Cut.all fun p : Fin 3 × Fin 3 =>
      Cut.all fun _ : wt p.1 p.2 < 0 => Cut.eq (O := O) ((conjBy h⁻¹ r g).mat p.1 p.2) 0)
    (Cut.all fun s => Cut.all fun _ : s ∈ I => Cut.all fun _ : η s = 1 => Cut.all fun a : Fin 3 =>
      Cut.eq (O := O) ((conjBy h⁻¹ r s).mat a a) (algebraMap O R (psi Ψ a s)))
  have CL := Cut.all fun g => Cut.all fun _ : g ∈ η.ker => Cut.all fun p : Fin 3 × Fin 3 =>
      Cut.all fun _ : 0 < wt p.1 p.2 => Cut.eq (O := O) ((conjBy h⁻¹ r g).mat p.1 p.2) 0
  have hcan : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'),
      Canon (UnitaryThreeInertia.push f r x).mat (GeneralLinearGroup.map (f : R →+* R') h) := by
    intro R' _ _ _ f
    haveI := locHom f
    rw [show (UnitaryThreeInertia.push f r x).mat = (r x).mat.map f from GG.map_mat _ _]
    exact canon_map.1 (f : R →+* R') _ h hh
  refine ⟨Cut.congr CT ?_, Cut.congr (Cut.and CT CL) ?_⟩
  · intro R' _ _ _ f
    beta_reduce
    rw [(cond_iff_canon η Ψ I (UnitaryThreeInertia.push f r) x _ (red_push hr f) hx hu (hcan R' f)).1]
    constructor
    · rintro ⟨ht, hi⟩
      refine ⟨fun g hg p hp => ?_, fun s hs hs1 a => ?_⟩
      · have e := ht g hg p.1 p.2 hp
        rw [conj_push] at e
        rw [e, map_zero]
      · have e := hi s hs hs1 a
        rw [conj_push] at e
        rw [e, AlgHom.commutes]
    · rintro ⟨ht, hi⟩
      refine ⟨fun g hg a b hab => ?_, fun s hs hs1 a => ?_⟩
      · rw [conj_push, ht g hg (a, b) hab, map_zero]
      · rw [conj_push, hi s hs hs1 a, AlgHom.commutes]
  · intro R' _ _ _ f
    beta_reduce
    rw [(cond_iff_canon η Ψ I (UnitaryThreeInertia.push f r) x _ (red_push hr f) hx hu (hcan R' f)).2]
    constructor
    · rintro ⟨⟨ht, hi⟩, hl⟩
      refine ⟨⟨fun g hg p hp => ?_, fun s hs hs1 a => ?_⟩, fun g hg p hp => ?_⟩
      · have e := ht g hg p.1 p.2 hp
        rw [conj_push] at e
        rw [e, map_zero]
      · have e := hi s hs hs1 a
        rw [conj_push] at e
        rw [e, AlgHom.commutes]
      · have e := hl g hg p.1 p.2 hp
        rw [conj_push] at e
        rw [e, map_zero]
    · rintro ⟨⟨ht, hi⟩, hl⟩
      refine ⟨⟨fun g hg a b hab => ?_, fun s hs hs1 a => ?_⟩, fun g hg a b hab => ?_⟩
      · rw [conj_push, ht g hg (a, b) hab, map_zero]
      · rw [conj_push, hi s hs hs1 a, AlgHom.commutes]
      · rw [conj_push, hl g hg (a, b) hab, map_zero]

private theorem cut_U {D : Type} [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R)
    (hr : Red η Ψ r) : Cut O R fun _ _ _ _ f => CondU η Ψ I (UnitaryThreeInertia.push f r) := by
  refine Cut.congr (Cut.all fun s => Cut.all fun _ : s ∈ kerBar η Ψ I => Cut.all fun p : Fin 3 × Fin 3 =>
    Cut.eq ((r s).mat p.1 p.2) ((1 : Matrix (Fin 3) (Fin 3) R) p.1 p.2)) ?_
  intro R' _ _ _ f
  beta_reduce
  have hone : ∀ a b, f ((1 : Matrix (Fin 3) (Fin 3) R) a b) = (1 : Matrix (Fin 3) (Fin 3) R') a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have key : ∀ s, η s = 1 → (UnitaryThreeInertia.push f r s = 1 ↔
      ∀ p : Fin 3 × Fin 3, f ((r s).mat p.1 p.2) = f ((1 : Matrix (Fin 3) (Fin 3) R) p.1 p.2)) := by
    intro s hs
    have hright : (UnitaryThreeInertia.push f r s).right = 1 := by
      show ((GG.map (f : R →+* R')) (r s)).right = 1
      rw [GG.map_right, hr.mult s, hs]
    have hmat : (UnitaryThreeInertia.push f r s).mat = (r s).mat.map f := GG.map_mat _ _
    constructor
    · intro h p
      have h' : (UnitaryThreeInertia.push f r s).mat = 1 := by
        rw [h]
        rfl
      have hp := congrFun (congrFun h' p.1) p.2
      rw [hmat, Matrix.map_apply] at hp
      rw [hp, hone]
    · intro h
      apply SemidirectProduct.ext
      · apply Units.ext
        show (UnitaryThreeInertia.push f r s).mat = 1
        rw [hmat]
        ext a b
        rw [Matrix.map_apply, h (a, b), hone]
      · exact hright
  constructor
  · intro H s hs p
    have hη : η s = 1 := hs.1.2
    exact (key s hη).mp (H s hs) p
  · intro H s hs
    have hη : η s = 1 := hs.1.2
    exact (key s hη).mpr (H s hs)

private theorem cut_N {D : Type} [Group D] (c g : D) (r : D →* GG 3 R) :
    Cut O R fun _ _ _ _ f => Normalised c g (UnitaryThreeInertia.push f r) := by
  refine Cut.congr (Cut.and
    (Cut.all fun p : Fin 3 × Fin 3 => Cut.eq ((r c).mat p.1 p.2) ((1 : Matrix (Fin 3) (Fin 3) R) p.1 p.2))
    (Cut.and (Cut.eq (zmat c g r 0 1) 0) (Cut.eq (zmat c g r 1 0) 0))) ?_
  intro R' _ _ _ f
  beta_reduce
  have hm : ∀ x, (UnitaryThreeInertia.push f r x).mat = (r x).mat.map f := fun x => GG.map_mat _ _
  have hz : ∀ a b, zmat c g (UnitaryThreeInertia.push f r) a b = f (zmat c g r a b) := by
    intro a b
    simp [zmat, hm, Matrix.sub_apply, map_sub]
  have hone : ∀ a b, f ((1 : Matrix (Fin 3) (Fin 3) R) a b) = (1 : Matrix (Fin 3) (Fin 3) R') a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro h
    refine ⟨fun p => ?_, ?_, ?_⟩
    · have hp := congrFun (congrFun h.atc p.1) p.2
      rw [hm, Matrix.map_apply] at hp
      rw [hp, hone]
    · rw [← hz, h.z12, map_zero]
    · rw [← hz, h.z21, map_zero]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hm]
      ext a b
      rw [Matrix.map_apply, h1 (a, b), hone]
    · rw [hz, h2, map_zero]
    · rw [hz, h3, map_zero]

private theorem cut_pt {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι)
    (hx : ∀ v ∈ F.Tb, ∃ x : F.D v, F.ηv v x = 1 ∧ IsUnit ((F.Ψv v x : O) ^ 2 - 1)) (g₁ : Γ) (r : Γ →* GG 3 R)
    (hr : Red F.η F.Ψ r) (hc : UnitaryThreeInertia.AdicCont (maximalIdeal R) r) :
    Cut O R fun _ _ _ _ f => F.IsPt g₁ (UnitaryThreeInertia.push f r) := by
  have hloc : ∀ v, Red (F.ηv v) (F.Ψv v) (r.comp (F.loc v)) := fun v =>
    ⟨fun g => hr.mult (F.loc v g), fun g => hr.red (F.loc v g)⟩
  have hTD : ∀ v ∈ F.Tb,
      (Cut O R fun _ _ _ _ f => CondT (F.ηv v) (F.Ψv v) (F.Iv v) (UnitaryThreeInertia.push f (r.comp (F.loc v)))) ∧
      Cut O R fun _ _ _ _ f => CondD (F.ηv v) (F.Ψv v) (F.Iv v) (UnitaryThreeInertia.push f (r.comp (F.loc v))) := by
    intro v hv
    obtain ⟨x, hx1, hx2⟩ := hx v hv
    exact cut_TD _ _ _ _ (hloc v) x hx1 hx2
  have hvl : ∀ v, v = F.vl → v ∈ F.Tb := by
    intro v hv
    rw [hv]
    exact Set.mem_insert _ _
  have hsb : ∀ v, v ∈ F.Sb → v ∈ F.Tb := fun v hv => Set.mem_insert_of_mem _ hv
  refine Cut.congr (Cut.and (Cut.all fun v => Cut.and
      (Cut.all fun hv : v = F.vl => (hTD v (hvl v hv)).1)
      (Cut.and (Cut.all fun hv : v ∈ F.Sb => (hTD v (hsb v hv)).2)
        (Cut.all fun _ : v ∉ F.Tb => cut_U (F.ηv v) (F.Ψv v) (F.Iv v) _ (hloc v))))
    (cut_N F.c g₁ r)) ?_
  intro R' _ _ _ f
  beta_reduce
  constructor
  · intro h
    exact ⟨fun v => h.loc v, h.norm⟩
  · rintro ⟨hl, hn⟩
    exact ⟨⟨⟨red_push hr f, hl⟩, hn⟩, cont_push hc f⟩

private def Box {Γ : Type} [Group Γ] [TopologicalSpace Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (u : Γ →* GG 3 R) : Prop :=
  Red η Ψ u ∧ UnitaryThreeInertia.AdicCont (maximalIdeal R) u ∧
    ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (r : Γ →* GG 3 R'), Red η Ψ r →
      UnitaryThreeInertia.AdicCont (maximalIdeal R') r → ∃! f : R →ₐ[O] R', UnitaryThreeInertia.push f u = r

private theorem univ_of_box [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {G Γ ι : Type} [Group G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι)
    (hx : ∀ v ∈ F.Tb, ∃ x : F.D v, F.ηv v x = 1 ∧ IsUnit ((F.Ψv v x : O) ^ 2 - 1)) (g₁ : Γ) (u : Γ →* GG 3 R)
    (hu : Box F.η F.Ψ u) (h0 : F.IsPt g₁ (F.rz O)) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (u : Γ →* GG 3 R), F.IsUniv g₁ u := by
  obtain ⟨I, hI⟩ := cut_pt F hx g₁ u hu.1 hu.2.1
  obtain ⟨f0, hf0, -⟩ := hu.2.2 O (F.rz O) h0.toRed h0.cont
  have hpt0 : F.IsPt g₁ (UnitaryThreeInertia.push f0 u) := by
    rw [hf0]
    exact h0
  have hk0 : ∀ x ∈ I, f0 x = 0 := (hI O f0).mp hpt0
  haveI : Nontrivial (R ⧸ I) := by
    refine nontrivial_of_ne 1 0 fun h1 => ?_
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 := hk0 1 h1
    rw [map_one] at h2
    exact one_ne_zero h2
  haveI : IsCO O (R ⧸ I) :=
    co_quot O R (R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hcomp : ∀ (R' : Type) [CommRing R'] [Algebra O R'] (g : R ⧸ I →ₐ[O] R'),
      UnitaryThreeInertia.push g (UnitaryThreeInertia.push (Ideal.Quotient.mkₐ O I) u) = UnitaryThreeInertia.push (g.comp (Ideal.Quotient.mkₐ O I)) u := by
    intro R' _ _ g
    ext x : 1
    apply SemidirectProduct.ext
    · apply Units.ext
      show GG.mat (GG.map (g : R ⧸ I →+* R') (GG.map (Ideal.Quotient.mkₐ O I : R →+* R ⧸ I) (u x))) =
        GG.mat (GG.map ((g.comp (Ideal.Quotient.mkₐ O I) : R →ₐ[O] R') : R →+* R') (u x))
      rw [GG.map_mat, GG.map_mat, GG.map_mat]
      rfl
    · show (GG.map (g : R ⧸ I →+* R') (GG.map (Ideal.Quotient.mkₐ O I : R →+* R ⧸ I) (u x))).right =
        (GG.map ((g.comp (Ideal.Quotient.mkₐ O I) : R →ₐ[O] R') : R →+* R') (u x)).right
      rw [GG.map_right, GG.map_right, GG.map_right]
  refine ⟨R ⧸ I, inferInstance, inferInstance, inferInstance, UnitaryThreeInertia.push (Ideal.Quotient.mkₐ O I) u, ⟨?_, ?_⟩⟩
  · exact (hI _ (Ideal.Quotient.mkₐ O I)).mpr fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro R' _ _ _ r hr
    obtain ⟨f, hf, huniq⟩ := hu.2.2 R' r hr.toRed hr.cont
    have hk : ∀ x ∈ I, f x = 0 := (hI R' f).mp (by beta_reduce; rw [hf]; exact hr)
    have hlc : (Ideal.Quotient.liftₐ I f hk).comp (Ideal.Quotient.mkₐ O I) = f := AlgHom.ext fun x => rfl
    refine ⟨Ideal.Quotient.liftₐ I f hk, ?_, fun g hg => ?_⟩
    · show UnitaryThreeInertia.push (Ideal.Quotient.liftₐ I f hk) (UnitaryThreeInertia.push (Ideal.Quotient.mkₐ O I) u) = r
      rw [hcomp, hlc, hf]
    · apply Ideal.Quotient.algHom_ext O
      rw [hlc]
      apply huniq
      rw [← hcomp]
      exact hg

private theorem red_iff {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (r : Γ →* GG 3 R) :
    Red η Ψ r ↔ ∀ g, GG.map (res O R : R →+* ResidueField O) (r g) = rbar O η Ψ g := by
  have halg : ∀ a : O, res O R (algebraMap O R a) = residue O a := fun a => by
    rw [AlgHom.commutes]
    rfl
  have hbar : ∀ g, rbar O η Ψ g = GG.map (residue O) (r0 η Ψ g) := by
    intro g
    apply SemidirectProduct.ext
    · apply Units.ext
      show GG.mat (rbar O η Ψ g) = GG.mat (GG.map (residue O) (r0 η Ψ g))
      rw [GG.map_mat]
      ext i j
      show ((tor (ResidueField O) (barChar O Ψ g) : GL (Fin 3) (ResidueField O)) : Matrix _ _ _) i j =
        residue O ((((tor O (Ψ g)) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i j)
      rw [tor_val, tor_val]
      by_cases hij : i = j
      · subst hij
        simp only [diagonal_apply_eq, barChar, MonoidHom.comp_apply, ← map_zpow, Units.coe_map]
        rfl
      · simp [diagonal_apply_ne _ hij]
    · rfl
  have key : ∀ g, GG.map (res O R : R →+* ResidueField O) (r g) = rbar O η Ψ g ↔
      ((r g).right = η g ∧ ∀ a b, (r g).mat a b - algebraMap O R ((r0 η Ψ g).mat a b) ∈ maximalIdeal R) := by
    intro g
    rw [hbar]
    constructor
    · intro h
      have hr := congrArg SemidirectProduct.right h
      have hl := congrArg GG.mat h
      rw [GG.map_mat, GG.map_mat] at hl
      rw [GG.map_right, GG.map_right] at hr
      refine ⟨hr, fun a b => ?_⟩
      have hab := congrFun (congrFun hl a) b
      simp only [Matrix.map_apply] at hab
      rw [← res_eq_zero_iff O R, map_sub, halg, sub_eq_zero]
      exact hab
    · rintro ⟨hr, hm⟩
      apply SemidirectProduct.ext
      · apply Units.ext
        show GG.mat (GG.map (res O R : R →+* ResidueField O) (r g)) = GG.mat (GG.map (residue O) (r0 η Ψ g))
        rw [GG.map_mat, GG.map_mat]
        ext a b
        have hab := (res_eq_zero_iff O R _).mpr (hm a b)
        rw [map_sub, halg, sub_eq_zero] at hab
        simpa using hab
      · rw [GG.map_right, GG.map_right]
        exact hr
  simp_rw [key]
  constructor
  · intro h g
    exact ⟨h.mult g, fun a b => h.red g a b⟩
  · intro h
    exact ⟨fun g => (h g).1, fun g a b => (h g).2 a b⟩

omit [IsLocalRing O] [IsCO O R] in
private theorem cont_iff {Γ : Type} [Group Γ] [TopologicalSpace Γ] (J : Ideal R) (r : Γ →* GG 3 R) :
    UnitaryThreeInertia.AdicCont J r ↔ ∀ a b, Alg.AdicCont J fun g => (r g).mat a b := by
  constructor
  · intro H a b N
    exact (H N).comp (fun M => M a b)
  · intro H n
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro M0
    have e : (fun g => (r g).mat.map (Ideal.Quotient.mk (J ^ n))) ⁻¹' {M0} =
        ⋂ a, ⋂ b, (fun g => Ideal.Quotient.mk (J ^ n) ((r g).mat a b)) ⁻¹' {M0 a b} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      constructor
      · intro h a b
        rw [← h]
        rfl
      · intro h
        ext a b
        exact h a b
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => (H a b n).isOpen_fiber _

private theorem phi_quot {Γ : Type} [Group Γ] [TopologicalSpace Γ] (M : Subgroup Γ) [M.Normal] {l : ℕ}
    (h : PhiCond Γ l) : PhiCond (Γ ⧸ M) l := by
  intro H' hH'
  let ψ : (H'.comap (QuotientGroup.mk' M)) →* H' := (QuotientGroup.mk' M).subgroupComap H'
  have hψc : Continuous ψ :=
    Continuous.subtype_mk (QuotientGroup.continuous_mk.comp continuous_subtype_val) _
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hopen : IsOpen ((H'.comap (QuotientGroup.mk' M) : Subgroup Γ) : Set Γ) :=
    hH'.preimage QuotientGroup.continuous_mk
  haveI := h _ hopen
  let F : {φ : H' →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H')} →
      {φ : (H'.comap (QuotientGroup.mk' M)) →* Multiplicative (ZMod l) //
        IsOpen (φ.ker : Set (H'.comap (QuotientGroup.mk' M)))} :=
    fun φ => ⟨φ.1.comp ψ, by
      rw [← MonoidHom.comap_ker]
      exact φ.2.preimage hψc⟩
  refine Finite.of_injective F ?_
  intro φ₁ φ₂ he
  apply Subtype.ext
  ext y
  obtain ⟨x, rfl⟩ := hψs y
  exact congrArg (fun φ => φ.1 x) he

private theorem box_of_univ {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}
    (U : Univ (Kills (O := O) (η := η) (Ψ := Ψ) ∅)) : Box η Ψ U.r.hom := by
  refine ⟨(red_iff _ _ _).2 U.r.red, (cont_iff _ _).2 U.r.cont, fun R' _ _ _ r hr hc => ?_⟩
  obtain ⟨f, hf, hf'⟩ := (U.rep R').2 ⟨r, (cont_iff _ _).1 hc, (red_iff _ _ _).1 hr⟩ fun _ h => h.elim
  exact ⟨f, congrArg GLift.hom hf, fun f' h' => hf' f' (GLift.ext h')⟩

end
end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.exists_isUniv :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (l : ℕ), l.Prime → (l : O) ∈ maximalIdeal O → PhiCond Γ l → ∀ g₁, F.Marked g₁ → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (u : Γ →* GG 3 R), F.IsUniv g₁ u := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF l hl hm hΦ g₁ _
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP (ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (residue O), residue_eq_zero_iff]; exact hm)
  have hΨ : IsLocallyConstant (barChar O F.Ψ) :=
    IsLocallyConstant.desc _ Units.val
      ((hF.Ψ_cont 1).comp (Ideal.Quotient.factor (pow_one (maximalIdeal O)).le)) Units.val_injective
  haveI : (Subgroup.normalClosure (∅ : Set Γ)).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  obtain ⟨U⟩ := exists_univ l F.η F.Ψ hF.η_cont hΨ ∅ (fun _ h => h.elim) _ rfl (phi_quot _ hΦ)
  exact univ_of_box F hF.x g₁ U.r.hom (box_of_univ U) (isPt_rz F hF g₁)
