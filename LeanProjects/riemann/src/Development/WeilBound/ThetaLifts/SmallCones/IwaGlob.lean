import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.TowerModels.ExistsRefl
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Euler
open PositivityTheory.ThKG.Tow.Levi (hf hf_apply hf_mulVec iso_of_hf exists_move piInf_incl piInf_cA iso_map_piInf exists_lift exists_inf ad_ext)
open PositivityTheory.ThK (latW KAt)

namespace IwaG

theorem exists_loc {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (hθ : IsCartan M θ)
    {v : Fin n → ℂ} (hv0 : v ≠ 0) (hvv : hf M v v = 0) {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g * g' = 1)
    (h2 : gᵀ * M * g.map star = M) :
    ∃ (p p' : Matrix (Fin n) (Fin n) ℂ) (t : ℂ), t ≠ 0 ∧ p * p' = 1 ∧ pᵀ * M * p.map star = M ∧ p *ᵥ v = t • v ∧
      Commute (p' * g) θ := by
  have hd := cartan_det hθ
  obtain ⟨c1, c2, c3⟩ := hθ
  have hgv : g *ᵥ (g' *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  obtain ⟨κ, t, ht, k1, k2, k3⟩ := exists_move hM c1 c2 c3 hv0 (v' := g' *ᵥ v)
    (fun h => hv0 (by rw [← hgv, h, Matrix.mulVec_zero])) hvv (by rw [← h2, ← hf_mulVec, hgv, hvv])
  have hκ : IsUnit κ.det := by
    have e := congrArg Matrix.det k1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e
    refine IsUnit.mk0 _ fun h => hd ?_
    rw [h, zero_mul, zero_mul] at e
    exact e.symm
  have h1' := mul_eq_one_comm.1 h1
  refine ⟨g * κ, κ⁻¹ * g', t, ht, ?_, iso_of_hf fun x y => ?_, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc κ, Matrix.mul_nonsing_inv _ hκ, one_mul, h1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf_mulVec, h2, hf_mulVec, k1]
  · rw [← Matrix.mulVec_mulVec, k3, Matrix.mulVec_smul, hgv]
  · rw [mul_assoc, h1', mul_one]
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det κ).2 hκ
    rw [← Matrix.coe_units_inv]
    exact k2.units_inv_left

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n r s : ℕ} {X : Spc F E n} {x : Fin n → E} {v : Pl F}

theorem compFin_smul (u : Pl F) (a : AF F) (z : AE F E) : compFin F E u (a • z) = evFin F u a • compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F u) a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem compInf_smul (u : InfinitePlace F) (a : AF F) (z : AE F E) : compInf F E u (a • z) = evInf F u a • compInf F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F u) a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def LocIwa (σ : E →ₐ[F] E) (X : Spc F E n) (x : Fin n → E) : Prop :=
  ∀ (v : Pl F) (g : UA σ X.J), g ∈ UAt σ X (evFin F v) → ∃ p ∈ UAt σ X (evFin F v), ∃ k ∈ KAt σ X v, ∃ t : (AE F E)ˣ,
    mat p *ᵥ incV F x = t.1 • incV F x ∧ g = p * k

theorem map_one' {S : Type} [CommRing S] (f : AE F E →+* S) : (1 : Matrix (Fin n) (Fin n) (AE F E)).map f = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem exists_arch (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hx : x ≠ 0) (h0 : form σ X.J x x = 0) (g : UA σ X.J) :
    ∃ (p : UA σ X.J) (t : (AE F E)ˣ), mat p *ᵥ incV F x = t.1 • incV F x ∧
      ∀ w, Commute ((mat (p⁻¹ * g)).map (piInf (B.emb w))) (X.θ w) := by
  have hσ := hB.cm
  choose p p' t ht h1 h2 h3 h4 using fun w => exists_loc (M := X.J.map (B.emb w).1)
    (fun i j => by rw [Matrix.map_apply, ← hσ.2.2.2, hX.herm, Matrix.map_apply]) (hX.cartan w)
    (v := fun i => (B.emb w).1 (x i))
    (fun h => hx (funext fun i => (B.emb w).1.injective ((congrFun h i).trans (map_zero _).symm)))
    (by
      have e := congrArg (B.emb w).1 h0
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ.2.2.2, map_zero] at e
      exact e)
    (g := (mat g).map (piInf (B.emb w))) (g' := (mat g⁻¹).map (piInf (B.emb w)))
    (by rw [← Matrix.map_mul, show mat g * mat g⁻¹ = 1 from g.1.mul_inv, map_one'])
    (by
      rw [← iso_map_piInf (fun τ z => piInf_cA hσ τ z), show (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J from g.2]
      exact Matrix.ext fun i j => piInf_incl _ _)
  obtain ⟨q, q1, q2⟩ := exists_lift hσ B.emb X.J p p' h1 h2
  obtain ⟨a, a1, a2⟩ := exists_inf hσ B.emb t
  obtain ⟨b, b1, b2⟩ := exists_inf hσ B.emb fun w => (t w)⁻¹
  have hab : a * b = 1 := ad_ext hσ B.emb (fun w => by rw [map_mul, a1, b1, mul_inv_cancel₀ (ht w), map_one])
    fun v => by rw [map_mul, a2, b2, mul_one, map_one]
  refine ⟨q, ⟨a, b, hab, (mul_comm _ _).trans hab⟩, funext fun i => ad_ext hσ B.emb (fun w => ?_) fun v => ?_, fun w => ?_⟩
  · have e : piInf (B.emb w) ∘ incV F x = fun i => (B.emb w).1 (x i) := funext fun i => piInf_incl _ _
    rw [RingHom.map_mulVec, q1, e, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, a1]
    exact congrArg _ (congrFun e i).symm
  · rw [RingHom.map_mulVec, q2, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, a2, one_mul]
    rfl
  · have e : (mat q⁻¹).map (piInf (B.emb w)) = p' w := by
      have e1 : (mat q⁻¹).map (piInf (B.emb w)) * p w = 1 := by
        rw [← q1, ← Matrix.map_mul, show mat q⁻¹ * mat q = 1 from q.1.inv_mul, map_one']
      exact left_inv_eq_right_inv e1 (h1 w)
    rw [mat_mul, Matrix.map_mul, e]
    exact h4 w

theorem latW_le : latW X v ≤ latHat X := AddSubgroup.closure_mono (by
  rintro _ ⟨a, ha, hi, y, hy, rfl⟩
  have e : idem v * a = a := at_iff.1 ha
  have := idem_mem hi
  rw [e] at this
  exact ⟨a, this.1, this.2, y, hy, rfl⟩)

theorem idem_latW {z : Fin n → AE F E} (hz : z ∈ latHat X) : idem v • z ∈ latW X v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hi, y, hy, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨idem v * a, at_iff.2 (by rw [smul_eq_mul, ← mul_assoc, idem_sq]), by
      rw [map_mul, ev_self, one_mul]; exact hi v, y, hy, by rw [smul_smul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

theorem int_of_KAt {k : UA σ X.J} (hk : k ∈ KAt σ X v) : IntAt v k := fun z hz h =>
  have h1 : z ∈ latW X v := at_iff.1 h ▸ idem_latW hz
  ⟨latW_le (hk.2 z h1).1, latW_le (hk.2 z h1).2⟩

variable (F) in

def eInf : AF F := ((1, 0) : Ainf F × Af F)

theorem eInf_smul {z : Fin n → AE F E} (hz : z ∈ latHat X) : eInf F • z = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    have h1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
    have : eInf F * a = 0 := Prod.ext ((one_mul a.1).trans h1) (zero_mul a.2)
    rw [smul_smul, this, zero_smul]
  | zero => rw [smul_zero]
  | add a b _ _ ha hb => rw [smul_add, ha, hb, add_zero]
  | neg a _ ha => rw [smul_neg, ha, neg_zero]

theorem glue (hL : X.L.IsLattice E) {z : Fin n → AE F E} (h0 : eInf F • z = 0) (h : ∀ v : Pl F, idem v • z ∈ latHat X) :
    z ∈ latHat X := by
  obtain ⟨m, y, -, hy⟩ := lat_gen (Y := X) hL
  choose a a1 a2 using fun v => (hy _).1 (h v)
  let b : Fin m → AF F := fun i => ((0, ⟨fun v => evFin F v (a v i), Eventually.of_forall fun v => (a1 v i).2 v⟩) : Ainf F × Af F)
  have hb : ∀ v i, evFin F v (b i) = evFin F v (a v i) := fun _ _ => rfl
  refine (hy _).2 ⟨b, fun i => ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => (a1 v i).2 v⟩,
    funext fun j => Supp.adTens_ext (fun w => ?_) fun v => ?_⟩
  · have e := congrArg (compInf F E w) (congrFun h0 j)
    rw [Pi.smul_apply, compInf_smul, show evInf F w (eInf F) = 1 from rfl, one_smul, Pi.zero_apply, map_zero] at e
    rw [e, Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [Pi.smul_apply, compInf_smul, show evInf F w (b i) = 0 from rfl, zero_smul]
  · have e := congrArg (compFin F E v) (congrFun (a2 v) j)
    rw [Pi.smul_apply, compFin_smul, ev_self, one_smul] at e
    rw [← e, Finset.sum_apply, Finset.sum_apply, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, Pi.smul_apply, compFin_smul, compFin_smul, hb]

theorem stab_of_int (hL : X.L.IsLattice E) {A : Matrix (Fin n) (Fin n) (AE F E)}
    (h : ∀ v, ∀ z ∈ latHat X, At (evFin F v) z → A *ᵥ z ∈ latHat X) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    A *ᵥ z ∈ latHat X :=
  glue hL (by rw [← Matrix.mulVec_smul, eInf_smul hz, Matrix.mulVec_zero]) fun v => by
    rw [← Matrix.mulVec_smul]
    exact h v _ (latW_le (idem_latW hz)) (at_iff.2 (by rw [smul_smul, idem_sq]))

theorem piInf_loc {p : UA σ X.J} (hp : p ∈ UAt σ X (evFin F v)) {w : InfinitePlace F} (τ : EmbOver E w) :
    (mat p).map (piInf τ) = 1 := by
  rw [← map_one' (piInf τ)]
  ext i j
  have e : idem v • (mat p - 1) i j = (mat p - 1) i j := congrFun (congrFun (at_iff.1 hp) i) j
  rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, ← Matrix.sub_apply, ← e, piInf,
    RingHom.comp_apply, compInf_smul, show evInf F w (idem v) = 0 from rfl, zero_smul, map_zero]

theorem exists_fin (B : Base F E) (hl : LocIwa σ X x) (S : Finset (Pl F)) :
    ∀ g : UA σ X.J, (∀ v ∉ S, IntAt v g) → ∃ (p : UA σ X.J) (t : (AE F E)ˣ), mat p *ᵥ incV F x = t.1 • incV F x ∧
      (∀ w, (mat p⁻¹).map (piInf (B.emb w)) = 1) ∧ ∀ v, IntAt v (p⁻¹ * g) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact fun g h => ⟨1, 1, by simp [mat_one], fun w => map_one' _, fun v => by simpa using h v (by simp)⟩
  | insert v S hv ih =>
    intro g h
    have hg : prj v g ∈ UAt σ X (evFin F v) := at_iff.2 (cut_eq.1 (congrArg mat (mem_loc.1 (prj_mem g))))
    obtain ⟨p, hp, k, hk, t, ht, e⟩ := hl v _ hg
    have hp' : p⁻¹ ∈ locGrp σ X v := inv_mem (Subgroup.subset_closure hp)
    obtain ⟨q, t', h1, h2, h3⟩ := ih (p⁻¹ * g) fun u hu => by
      by_cases c : u = v
      · subst c
        rw [← int_prj, map_mul, mem_loc.1 hp', e, inv_mul_cancel_left]
        exact int_of_KAt hk
      · exact (int_mul_ne c hp' g).2 (h u (by simp [c, hu]))
    refine ⟨p * q, t' * t, ?_, fun w => ?_, fun u => by rw [mul_inv_rev, mul_assoc]; exact h3 u⟩
    · rw [mat_mul, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, ht, smul_smul, Units.val_mul]
    · rw [mul_inv_rev, mat_mul, Matrix.map_mul, h2, piInf_loc (at_iff.2 (cut_eq.1 (congrArg mat (mem_loc.1 hp')))), mul_one]

theorem iwa_glob {n₁ : ℕ} {H : Plane E n n₁} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hx : H.x ≠ 0)
    (h0 : form σ X.J H.x H.x = 0) (hl : LocIwa σ X H.x) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (g : UA σ X.J) :
    ∃ (p k : UA σ X.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k := by
  obtain ⟨q, t, h1, h2⟩ := exists_arch hB hX hx h0 g
  have hf : ∀ᶠ v in cofinite, IntAt v (q⁻¹ * g) := by
    filter_upwards [ae_mulVec hX.lat (mat (q⁻¹ * g)), ae_mulVec hX.lat (mat (q⁻¹ * g)⁻¹)] with v a b z hz h
    exact ⟨a z hz h, b z hz h⟩
  obtain ⟨p, t', e1, e2, e3⟩ := exists_fin B hl (Set.Finite.toFinset hf) (q⁻¹ * g) fun v hv =>
    not_not.1 fun c => hv ((Set.Finite.mem_toFinset hf).2 c)
  refine ⟨q * p, p⁻¹ * (q⁻¹ * g), t' * t, (hK _).2 ⟨fun w => ?_, fun z hz => ⟨?_, ?_⟩⟩, ?_, by group⟩
  · rw [mat_mul, Matrix.map_mul, e2, one_mul]
    exact h2 w
  · exact stab_of_int hX.lat (fun v z hz h => (e3 v z hz h).1) hz
  · exact stab_of_int hX.lat (fun v z hz h => (e3 v z hz h).2) hz
  · rw [mat_mul, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_smul, h1, smul_smul, Units.val_mul]

end IwaG

end PositivityTheory.ThKCT

end
