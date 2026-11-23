import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.MemLineStab
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.ExistsSelfDual
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Inertof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace PositivityTheory.ThKG.Loc.Iwa

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.ThK PositivityTheory.ThKH.Iwas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

theorem mem_iff {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AE F E)) :
    g ∈ HR (AF F) σ (ξ • Jᵀ) ↔ g ∈ UG (cA σ) (incM F J) := by
  have e : JR (AF F) (ξ • Jᵀ) = inclR (F := F) (AF F) ξ • (incM F J)ᵀ := by
    ext i j; exact map_mul (inclR (F := F) (AF F)) _ _
  have u : IsUnit (inclR (F := F) (AF F) ξ) := (IsUnit.mk0 ξ hξ).map _
  change (g.1.map (cA σ))ᵀ * JR (AF F) (ξ • Jᵀ) * g.1 = JR (AF F) (ξ • Jᵀ) ↔ g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J
  rw [e, Matrix.mul_smul, Matrix.smul_mul, u.smul_left_cancel, ← Matrix.transpose_inj]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

omit [NumberField E] in
theorem compFin_smul (u : Pl F) (a : AF F) (z : AE F E) : compFin F E u (a • z) = evFin F u a • compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F u) a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [NumberField E] in
theorem compInf_smul (u : InfinitePlace F) (a : AF F) (z : AE F E) : compInf F E u (a • z) = evInf F u a • compInf F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F u) a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem at_emb {J : Matrix (Fin n) (Fin n) E} (z : GLoc σ J v) : At (evFin F v) ((matHom _ σ J (emb σ J v z)).1 - 1) := by
  intro a ha
  ext i j
  have one : ∀ {S : Type} [CommRing S] (f : AE F E →+* S), f ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j) =
      (1 : Matrix (Fin n) (Fin n) S) i j := fun f => congrFun (congrFun (Matrix.map_one f (map_zero _) (map_one _)) i) j
  change a • ((matHom _ σ J (emb σ J v z)).1 i j - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = 0
  refine Supp.adTens_ext (fun w => ?_) fun u => ?_
  · have := congrArg (fun x => (matHom _ σ J x).1 i j) (projArch_emb σ J w v z)
    rw [compInf_smul, map_sub, one, map_zero]
    exact smul_eq_zero_of_right _ (sub_eq_zero.2 this)
  · rw [compFin_smul, map_zero]
    by_cases h : u = v
    · subst h; rw [ha, zero_smul]
    · have := congrArg (fun x => (matHom _ σ J x).1 i j) (proj_emb_ne σ J h z)
      rw [map_sub, one]
      exact smul_eq_zero_of_right _ (sub_eq_zero.2 this)

theorem mem_latW_iff' (W : Spc F E n) (y : Fin n → AE F E) :
    y ∈ latW W v ↔ At (evFin F v) y ∧ (fun i => compFin F E v (y i)) ∈ latLoc F W.L v := by
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hi, x, hx, rfl⟩ := hz
      refine ⟨fun u hu => funext fun i => ?_, ?_⟩
      · change u • a • inclR (F := F) (AF F) (x i) = 0
        rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      · convert tmul_mem_latLoc hi hx using 2 with i
        rw [compFin_smul]
        change evFin F v a • (evFin F v 1 ⊗ₜ[F] x i) = _
        rw [map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | zero => exact ⟨at_zero, by simp only [Pi.zero_apply, map_zero]; exact zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨at_add ha.1 hb.1, by simp only [Pi.add_apply, map_add]; exact add_mem ha.2 hb.2⟩
    | neg a _ ha => exact ⟨by simpa using at_sub at_zero ha.1, by simp only [Pi.neg_apply, map_neg]; exact neg_mem ha.2⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ z ∈ latLoc F W.L v, (fun i => sgE E v (z i)) ∈ latW W v := fun z hz => by
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨sg v a, at_sg a, by rw [ev_sg]; exact ha, x, hx, funext fun i => ?_⟩
        change sg v a ⊗ₜ[F] x i = (sg v a * 1) ⊗ₜ[F] x i
        rw [mul_one]
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add a b _ _ ha hb => simp only [Pi.add_apply, map_add]; exact add_mem ha hb
      | neg a _ ha => simp only [Pi.neg_apply, map_neg]; exact neg_mem ha
    convert key _ h2 using 1
    funext i
    refine sub_eq_zero.1 (eq_zero_of_at (v := v) (at_sub (fun u hu => congrFun (h1 u hu) i) (at_sgE _)) ?_)
    rw [map_sub, comp_sgE, sub_self]

theorem stab_latW {Y : Spc F E n} {k : UA σ Y.J} (hk : k ∈ UAt σ Y (evFin F v)) {κ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (e : (mat k).map (compFin F E v) = κ) (h : ∀ z ∈ latLoc F Y.L v, κ *ᵥ z ∈ latLoc F Y.L v) :
    ∀ y ∈ latW Y v, mat k *ᵥ y ∈ latW Y v := fun y hy => by
  obtain ⟨h1, h2⟩ := (mem_latW_iff' Y y).1 hy
  refine (mem_latW_iff' Y _).2 ⟨at_mulVec_right _ h1, ?_⟩
  convert h _ h2 using 1
  funext i
  rw [← e]
  exact RingHom.map_mulVec (compFin F E v) _ y i

def bk {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) : GAd σ (ξ • Jᵀ) →* UA σ J where
  toFun z := ⟨matHom _ σ _ z, (mem_iff hξ _ _).1 z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mat_bk {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) (z : GAd σ (ξ • Jᵀ)) :
    mat (bk hξ J z) = (matHom _ σ _ z).1 := rfl

theorem bk_surj {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) : ∃ z, bk (σ := σ) hξ J z = g :=
  ⟨⟨g.1, (mem_iff hξ _ _).2 g.2⟩, rfl⟩

theorem iwaLoc {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    {x : Fin n → E} (hx : x ≠ 0) (h0 : form σ Y.J x x = 0) (v : Pl F) {g : UA σ Y.J} (hg : g ∈ UAt σ Y (evFin F v)) :
    ∃ p ∈ UAt σ Y (evFin F v), ∃ k ∈ KAt σ Y v, ∃ t : (AE F E)ˣ,
      mat p *ᵥ GlobalTheory.ThK.incV F x = t.1 • GlobalTheory.ThK.incV F x ∧ g = p * k := by
  obtain ⟨ξ, hξ, hJ, hL⟩ := exists_selfDual hB hY v
  haveI := hB.unram
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance
  haveI : Y.L.IsLattice E := hY.elim (·.lat) (·.lat)
  obtain ⟨g', rfl⟩ := bk_surj hξ Y.J g
  obtain ⟨q, k, ⟨t, ht⟩, hk, e⟩ := core hB.cm hθ hJ Y.L (unramAt hB v)
    ((isEmpty_or_nonempty _).symm.imp_right (inert_of_local F E σ B hB v)) hL hx (by
      have := hE_smul (σ := σ) ξ Y.J x x
      rw [h0, mul_zero] at this
      rw [← this]
      simp only [hE, Formalism.UG.hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
      exact Finset.sum_comm) (proj σ _ v g')
  have cmp : ∀ z : GLoc σ (ξ • Y.Jᵀ) v, (mat (bk hξ Y.J (emb σ _ v z))).map (compFin F E v) = (matHom _ σ _ z).1 := fun z => by
    rw [mat_bk]
    exact congrArg (fun x => (matHom _ σ _ x).1) (proj_emb_self σ _ v z)
  have hat : ∀ z : GLoc σ (ξ • Y.Jᵀ) v, bk hξ Y.J (emb σ _ v z) ∈ UAt σ Y (evFin F v) := fun z => by
    change At _ (mat _ - 1)
    rw [mat_bk]
    exact at_emb z
  refine ⟨_, hat q, _, ⟨hat k, fun y hy => ⟨stab_latW (hat k) (cmp k) (fun z hz => (hk z).1 hz) y hy, ?_⟩⟩, t,
    by rw [mat_bk]; exact ht, ?_⟩
  · rw [← map_inv, ← map_inv]
    have hk' : k⁻¹ ∈ stabLoc σ _ Y.L v := inv_mem hk
    exact stab_latW (hat k⁻¹) (cmp k⁻¹) (fun z hz => (hk' z).1 hz) y hy
  · rw [← map_mul, ← map_mul, ← e]
    have c1 := cmp (proj σ _ v g')
    have a1 := at_sub hg (hat (proj σ _ v g'))
    have c2 : (mat (bk hξ Y.J g')).map (compFin F E v) = (matHom _ σ _ (proj σ _ v g')).1 := by rw [mat_bk]; rfl
    rw [← c2] at c1
    generalize bk hξ Y.J (emb σ _ v (proj σ _ v g')) = a at c1 a1
    generalize bk hξ Y.J g' = b at c1 a1
    rw [sub_sub_sub_cancel_right] at a1
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_at (v := v) (fun u hu => ?_) ?_)))
    · exact congrFun (congrFun (a1 u hu) i) j
    · rw [map_sub, sub_eq_zero]
      exact (congrFun (congrFun c1 i) j).symm

end PositivityTheory.ThKG.Loc.Iwa

end
