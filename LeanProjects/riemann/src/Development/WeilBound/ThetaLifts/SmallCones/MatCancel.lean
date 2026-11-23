import Development.WeilBound.ThetaLifts.SmallCones.ColsOfMul
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Fr

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open PositivityTheory.ThKG.Tow.Levi (sig_sig cA_cA exists_UA)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_det {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := fun hm => by
  obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hm
  have := h.2.2 (star x) (by simpa using hx)
  rw [star_star, e, dotProduct_zero] at this
  exact lt_irrefl _ this

variable {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ r s : ℕ}

theorem det_ne (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) : Y.J.det ≠ 0 := by
  obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
  rcases hY with h | h
  · intro h0
    refine cartan_det (h.cartan u) ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · exact PositivityTheory.ThKG.Tow.Levi.det_ne_zero h

theorem exists_eps (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) :
    ∃ ε : ℤˣ, (∀ i j, σ (Y.J j i) = ((ε : ℤ) : E) * Y.J i j) ∧ Y.L.IsLattice E := by
  rcases hY with h | h
  · exact ⟨1, fun i j => by simp [h.herm], h.lat⟩
  · exact ⟨-1, fun i j => by simp [h.skew], h.lat⟩

theorem form_eps (hs : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {ε : ℤˣ}
    (hJ : ∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) (x y : Fin n → E) :
    σ (form σ J y x) = ((ε : ℤ) : E) * form σ J x y := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, hs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hJ]; ring

theorem eps_sq (ε : ℤˣ) : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem isFr (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    ∃ (ε : E) (A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E), IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A' := by
  obtain ⟨ε, hε, hL⟩ := exists_eps hY
  have hsk : ∀ x y, form σ Y.J x y = ((ε : ℤ) : E) * σ (form σ Y.J y x) := fun x y => by
    rw [form_eps (sig_sig hB.cm) hε, ← mul_assoc, eps_sq, one_mul]
  have ent : ∀ a b, ((fr H.ι H.x H.y)ᵀ * Y.J * (fr H.ι H.x H.y).map (σ : E →+* E)) a b =
      form σ Y.J (fun i => fr H.ι H.x H.y i a) (fun i => fr H.ι H.x H.y i b) := fun a b => by
    rw [Matrix.mul_assoc]; rfl
  have col : ∀ j, (fun i => fr H.ι H.x H.y i (Sum.inl j)) = H.ι *ᵥ Pi.single j 1 := fun j => by
    ext i; simp [fr]
  have hs : ∀ z : Fin n → E, z ∈ LinearMap.range (Matrix.toLin' (fr H.ι H.x H.y)) := fun z => by
    have hz : z ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
    refine (Submodule.span_le.2 fun z hz => ?_) hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    exact ⟨Sum.elim u ![s, t], by rw [Matrix.toLin'_apply, fr_mulVec]; abel⟩
  choose f hf using fun j => hs (Pi.single j 1)
  have h1 : fr H.ι H.x H.y * (Matrix.of fun a j => f j a) = 1 := by
    ext i j
    rw [Matrix.one_apply, ← Pi.single_apply, ← hf j]; rfl
  refine ⟨(ε : ℤ), _, eps_sq ε, ?_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h1⟩
  ext (a | a) (b | b)
  · exact congrFun (congrFun hH.gram a) b
  · rw [ent, col]
    fin_cases b
    exacts [(hH.orth _).1, (hH.orth _).2]
  · rw [ent, col, hsk]
    fin_cases a
    · exact (congrArg (fun z => _ * σ z) (hH.orth _).1).trans (by simp [gr])
    · exact (congrArg (fun z => _ * σ z) (hH.orth _).2).trans (by simp [gr])
  · rw [ent]
    fin_cases a <;> fin_cases b
    exacts [hH.xx, hH.xy, (hsk _ _).trans ((congrArg (fun z => _ * σ z) hH.xy).trans (by simp [gr])), hH.yy]

variable {ε : E} {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E}

theorem IsFr.ad (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') :
    IsFr (cA σ : AE F E →+* AE F E) (inclR (F := F) (AF F) ε) (incM F Y.J) (incM F Y₁.J) (incM F H.ι) (incV F H.x) (incV F H.y)
      (incM F A') :=
  h.map (inclR (F := F) (AF F)) fun _ => rfl

theorem mat_mul {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inj {J : Matrix (Fin n) (Fin n) E} {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem mat_cancel {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (z : Fin n → AE F E) : mat g⁻¹ *ᵥ (mat g *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec]

theorem mat_cancel' {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (z : Fin n → AE F E) : mat g *ᵥ (mat g⁻¹ *ᵥ z) = z := by
  simpa using mat_cancel g⁻¹ z

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F ⊗[F] E) := by
    haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    infer_instance
  (inclR (F := F) (E := E) (AF F)).injective

theorem mem_ratU {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} : g ∈ ratU σ J ↔ ∃ M, mat g = incM F M := by
  refine ⟨fun h => ?_, fun ⟨M, hM⟩ => ?_⟩
  · obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 h
    exact ⟨u.1, (congrArg Units.val hu).symm⟩
  · haveI : Nontrivial (AE F E) := inclR_inj.nontrivial
    have h1 : IsUnit (mat g).det := (Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit
    have h2 : M.det ≠ 0 := fun h0 => by
      rw [hM, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
      exact not_isUnit_zero h1
    exact Subgroup.mem_subgroupOf.2 ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M h2, Units.ext hM.symm⟩

theorem mem_unip {u : UA σ Y.J} : u ∈ unip σ Y H ↔ mat u *ᵥ incV F H.x = incV F H.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨Matrix.one_mulVec _, fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  | mul a b _ _ ha hb =>
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hb.1, ha.1], fun z => ?_⟩
    obtain ⟨s, hs⟩ := ha.2 z
    obtain ⟨t, ht⟩ := hb.2 z
    exact ⟨s + t, by rw [mat_mul, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_add, hs, Matrix.mulVec_smul, ha.1, add_smul, add_assoc]⟩
  | inv a _ ha =>
    have e : mat a⁻¹ *ᵥ incV F H.x = incV F H.x := by conv_lhs => rw [← ha.1, mat_cancel]
    refine ⟨e, fun z => ?_⟩
    obtain ⟨s, hs⟩ := ha.2 z
    have := mat_cancel a (incM F H.ι *ᵥ z)
    rw [hs, Matrix.mulVec_add, Matrix.mulVec_smul, e] at this
    exact ⟨-s, by rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]⟩

theorem exists_levi (hσ : IsCMExt F E σ) (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') (t : (AE F E)ˣ) (g : UA σ Y₁.J) :
    ∃ m : UA σ Y.J, IsLevi H t g m ∧
      mat m = fr (incM F H.ι) (incV F H.x) (incV F H.y) * dg (mat g) t.1 (cA σ (t⁻¹).1) * incM F A' := by
  obtain ⟨m, m', e0, e1, e2, e3, e4, e5⟩ := h.ad.levi (cA_cA hσ) t.mul_inv g.1.mul_inv g.2
  obtain ⟨p, rfl⟩ := exists_UA e1 e2
  exact ⟨p, ⟨e3, e4, e5⟩, e0⟩

theorem levi_uniq (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m m' : UA σ Y.J}
    (h1 : IsLevi H t g m) (h2 : IsLevi H t g m') : m = m' :=
  mat_inj (h.ad.ext (h1.1.trans h2.1.symm) (h1.2.1.trans h2.2.1.symm) (h1.2.2.trans h2.2.2.symm))

theorem levi_mul {t t' : (AE F E)ˣ} {g g' : UA σ Y₁.J} {m m' : UA σ Y.J} (h1 : IsLevi H t g m) (h2 : IsLevi H t' g' m') :
    IsLevi H (t * t') (g * g') (m * m') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.1, Matrix.mulVec_smul, h1.1, smul_smul, Units.val_mul, mul_comm]
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.2.1, Matrix.mulVec_smul, h1.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [mat_mul, Matrix.mul_assoc, h2.2.2, ← Matrix.mul_assoc, h1.2.2, Matrix.mul_assoc, mat_mul]

theorem levi_one : IsLevi (W := Y) (W₁ := Y₁) (σ := σ) H 1 1 1 :=
  ⟨by simp [mat_one], by simp [mat_one], by simp [mat_one]⟩

theorem levi_inv {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) : IsLevi H t⁻¹ g⁻¹ m⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · have := mat_cancel m (incV F H.x)
    rw [h1.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, Units.inv_mul, one_smul]
  · have := mat_cancel m (incV F H.y)
    rw [h1.2.1, Matrix.mulVec_smul] at this
    conv_rhs => rw [← this, smul_smul, ← map_mul, inv_inv, Units.mul_inv, map_one, one_smul]
  · have : mat m⁻¹ * (incM F H.ι * mat g) = incM F H.ι := by
      rw [← h1.2.2, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    conv_rhs => rw [← this, Matrix.mul_assoc, Matrix.mul_assoc, ← mat_mul, mul_inv_cancel, mat_one, Matrix.mul_one]

theorem levi_vec {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) (z : Fin n₁ → AE F E) :
    mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat g *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, h1.2.2, Matrix.mulVec_mulVec]

theorem levi_conj {t : (AE F E)ˣ} {g : UA σ Y₁.J} {m : UA σ Y.J} (h1 : IsLevi H t g m) {u : UA σ Y.J} (hu : u ∈ unip σ Y H) :
    m⁻¹ * u * m ∈ unip σ Y H := by
  obtain ⟨a, b⟩ := mem_unip.1 hu
  have h2 := levi_inv h1
  refine mem_unip.2 ⟨?_, fun z => ?_⟩
  · rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1.1, Matrix.mulVec_smul, a, ← h1.1, mat_cancel]
  · obtain ⟨c, hc⟩ := b (mat g *ᵥ z)
    exact ⟨c * (t⁻¹).1, by rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, levi_vec h1, hc,
      Matrix.mulVec_add, levi_vec h2, mat_cancel, Matrix.mulVec_smul, h2.1, smul_smul]⟩

theorem stab_dec (hσ : IsCMExt F E σ) (h : IsFr (σ : E →+* E) ε Y.J Y₁.J H.ι H.x H.y A') (hd : Y.J.det ≠ 0) (p : UA σ Y.J)
    (t : (AE F E)ˣ) (hp : mat p *ᵥ incV F H.x = t.1 • incV F H.x) :
    ∃ u ∈ unip σ Y H, ∃ g₁ m, IsLevi (W₁ := Y₁) H t g₁ m ∧ p = u * m ∧
      mat g₁ = (incM F A' * mat p * fr (incM F H.ι) (incV F H.x) (incV F H.y)).toBlocks₁₁ := by
  obtain ⟨g, α, e0, hg, hα⟩ := h.ad.stab t.mul_inv p.2 hp
  have hgu : IsUnit g.det := by
    have e := congrArg Matrix.det hg
    have hd' : IsUnit (incM F Y₁.J).det := by
      have := (h.isUnit_det hd.isUnit).map (inclR (F := F) (AF F))
      rwa [RingHom.map_det] at this
    rw [← e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd'
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hd')
  obtain ⟨g₁, rfl⟩ := exists_UA (σ := σ) (Matrix.mul_nonsing_inv _ hgu) hg
  obtain ⟨m, hm, -⟩ := exists_levi hσ h t g₁
  have h2 := levi_inv hm
  refine ⟨p * m⁻¹, mem_unip.2 ⟨?_, fun z => ⟨α ⬝ᵥ (mat g₁⁻¹ *ᵥ z), ?_⟩⟩, g₁, m, hm, by group, e0⟩
  · rw [mat_mul, ← Matrix.mulVec_mulVec, h2.1, Matrix.mulVec_smul, hp, smul_smul, Units.inv_mul, one_smul]
  · rw [mat_mul, ← Matrix.mulVec_mulVec, levi_vec h2]
    exact (hα _).trans (by rw [mat_cancel'])

end PositivityTheory.ThKCT.Fr

end
