import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LevelActionPinned

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
  Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Algebra

variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A ≃+* B) (S : Subring B) (β : GL (Fin n) B)
  {P Q : AddSubgroup (Fin n → A)} {𝔞 : Set A}

theorem equiv_mulVec (m : Matrix (Fin n) (Fin n) A) (z : Fin n → A) :
    (fun i => e ((m *ᵥ z) i)) = m.map e *ᵥ fun i => e (z i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem mulVec_mem_of_frame (hP : ∀ z, z ∈ P ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => e (z i)) i ∈ S)
    (hQ : Q = AddSubgroup.closure {w | ∃ a ∈ 𝔞, ∃ z ∈ P, w = a • z}) (m : Matrix (Fin n) (Fin n) A)
    (T : Matrix (Fin n) (Fin n) S) (hm : m.map e = β.val * T.map S.subtype * (β⁻¹).val) :
    ∀ z ∈ Q, m *ᵥ z ∈ Q := by
  have h0 : ∀ z ∈ P, m *ᵥ z ∈ P := by
    intro z hz
    rw [hP] at hz ⊢
    intro i
    rw [equiv_mulVec, hm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
    exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (T i j).2 (hz j)
  subst hQ
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a, ha, m *ᵥ y, h0 y hy, Matrix.mulVec_smul m a y⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem mulVec_smul_congr (hP : ∀ z, z ∈ P ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => e (z i)) i ∈ S)
    (hQ : Q = AddSubgroup.closure {w | ∃ a ∈ 𝔞, ∃ z ∈ P, w = a • z}) (k : Matrix (Fin n) (Fin n) A)
    (y : Matrix (Fin n) (Fin n) S) (hk : k.map e = β.val * y.map S.subtype * (β⁻¹).val) {O : Type} [CommRing O]
    (f : O →+* S) {I J : Ideal O} {M : ℕ} (hM : I * J = Ideal.span {(M : O)}) (hy : ∀ i j, (y - 1) i j ∈ I.map f) {b₀ : O}
    (hb₀ : b₀ ∈ J) (b : A) (hb : e b = f b₀) :
    ∀ z ∈ Q, ∃ w ∈ Q, k *ᵥ (b • z) - b • z = M • w := by
  set b' := f b₀ with hb'
  have hy' : ∀ i j, ∃ t : S, t * M = b' * (y - 1) i j := fun i j => by
    have h := Ideal.mul_mem_mul (hy i j) (Ideal.mem_map_of_mem f hb₀)
    rw [← Ideal.map_mul, hM, Ideal.map_span, Set.image_singleton, map_natCast, mul_comm] at h
    exact Ideal.mem_span_singleton'.1 h
  choose T hT using hy'
  let m : Matrix (Fin n) (Fin n) A := (β.val * (Matrix.of T).map S.subtype * (β⁻¹).val).map e.symm
  have hm : m.map e = β.val * (Matrix.of T).map S.subtype * (β⁻¹).val := by
    ext i j; exact e.apply_symm_apply _
  have h1 : (M : B) • (Matrix.of T).map S.subtype = (b' : B) • (y.map S.subtype - 1) := by
    ext i j
    have := congrArg S.subtype (hT i j)
    by_cases hij : i = j <;> simpa [Matrix.one_apply, hij, mul_comm] using this
  have h2 : b • (k - 1) = (M : A) • m := by
    apply Matrix.map_injective e.injective
    have e1 : (b • (k - 1)).map e = e b • (k.map e - 1) := by
      ext i j; by_cases hij : i = j <;> simp [hij]
    have e2 : ((M : A) • m).map e = (M : B) • m.map e := by ext i j; simp
    show (b • (k - 1)).map e = ((M : A) • m).map e
    rw [e1, e2, hm, hk, hb, ← Matrix.smul_mul, ← Matrix.mul_smul, h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  intro z hz
  refine ⟨m *ᵥ z, mulVec_mem_of_frame e S β hP hQ m _ hm z hz, ?_⟩
  have := congrArg (· *ᵥ z) h2
  simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_sub] at this
  rw [Matrix.mulVec_smul, this]

theorem mulVec_mul_congr {k g h u : Matrix (Fin n) (Fin n) A} {x w : Fin n → A} {M : ℕ} (hk : k = g * (h * u))
    (hu : u *ᵥ x - x = M • w) : k *ᵥ x - g *ᵥ h *ᵥ x = M • g *ᵥ h *ᵥ w := by
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hu, Matrix.mulVec_sub, Matrix.mulVec_sub, hk, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]

theorem congr_of_matrices {O La G : Type} [CommRing O] [AddCommGroup La] [Module O La] [Group G] (fv : La →+ (Fin n → A))
    (M : ℕ) (Mb Mh : Ideal O) (hcop : Mb ⊔ Mh = ⊤) (hM₀ : Mb * Mh = Ideal.span {(M : O)}) (lev : G → La →ₗ[O] La)
    (κ : G → Matrix (Fin n) (Fin n) A) (hdiv : ∀ x, ∀ w ∈ Q, fv x = M • w → ∃ x', x = M • x')
    (hlev : ∀ g, ∀ a ∈ Mh • (⊤ : Submodule O La), ∃ w ∈ Q, fv (lev g a) - κ g *ᵥ fv a = M • w)
    (hpres : ∀ g, ∀ w ∈ Q, κ g *ᵥ w ∈ Q)
    (hone : ∀ a ∈ Mh • (⊤ : Submodule O La), ∃ w ∈ Q, κ 1 *ᵥ fv a - fv a = M • w)
    (hmul : ∀ g h, ∀ a ∈ Mh • (⊤ : Submodule O La), ∃ w ∈ Q, κ (g * h) *ᵥ fv a - κ g *ᵥ κ h *ᵥ fv a = M • w) :
    (∀ a, lev 1 a - a ∈ Mb • (⊤ : Submodule O La)) ∧
      ∀ g h a, lev (g * h) a - lev g (lev h a) ∈ Mb • (⊤ : Submodule O La) := by
  have hM : (M : O) ∈ Mb := Ideal.mul_le_left (I := Mb) (J := Mh) (by rw [hM₀]; exact Ideal.mem_span_singleton_self _)
  have key : ∀ f : La →ₗ[O] La, (∀ a ∈ Mh • (⊤ : Submodule O La), ∃ w ∈ Q, fv (f a) = M • w) →
      ∀ a, f a ∈ Mb • (⊤ : Submodule O La) := by
    intro f hf a
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : O) ∈ Mb ⊔ Mh)
    obtain ⟨w, hw, e₁⟩ := hf (v • a) (Submodule.smul_mem_smul hv Submodule.mem_top)
    obtain ⟨x, hx⟩ := hdiv _ w hw e₁
    have e₂ : f a = u • f a + (M : O) • x := by
      rw [Nat.cast_smul_eq_nsmul, ← hx, map_smul, ← add_smul, huv, one_smul]
    rw [e₂]
    exact add_mem (Submodule.smul_mem_smul hu Submodule.mem_top) (Submodule.smul_mem_smul hM Submodule.mem_top)
  refine ⟨key (lev 1 - LinearMap.id) fun a ha => ?_, fun g h => key (lev (g * h) - lev g ∘ₗ lev h) fun a ha => ?_⟩
  · obtain ⟨w₁, h₁, e₁⟩ := hlev 1 a ha
    obtain ⟨w₂, h₂, e₂⟩ := hone a ha
    refine ⟨w₁ + w₂, add_mem h₁ h₂, ?_⟩
    rw [smul_add, ← e₁, ← e₂, LinearMap.sub_apply, map_sub, LinearMap.id_apply]
    abel
  · have ha' : lev h a ∈ Mh • (⊤ : Submodule O La) := by
      have := Submodule.mem_map_of_mem (f := lev h) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    obtain ⟨w₁, h₁, e₁⟩ := hlev (g * h) a ha
    obtain ⟨w₂, h₂, e₂⟩ := hmul g h a ha
    obtain ⟨w₃, h₃, e₃⟩ := hlev h a ha
    obtain ⟨w₄, h₄, e₄⟩ := hlev g _ ha'
    refine ⟨w₁ + w₂ - κ g *ᵥ w₃ - w₄, sub_mem (sub_mem (add_mem h₁ h₂) (hpres g _ h₃)) h₄, ?_⟩
    rw [smul_sub, smul_sub, smul_add, ← Matrix.mulVec_smul, ← e₁, ← e₂, ← e₃, ← e₄, LinearMap.sub_apply, map_sub,
      LinearMap.comp_apply, Matrix.mulVec_sub]
    abel

end Algebra

def sw (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* Lev.EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

abbrev SI (D : D7) : Subring (Lev.EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

theorem mem_latHat_iff {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ latHat V ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => sw D (z i)) i ∈ SI D := by
  obtain ⟨c, hF, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  rw [← hF]
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      refine GlobalTheory.AdelicLatMove.pure_mem_hatL Λ a ha (fun i => V.frame.repr x i) (h1 _ ?_)
      show ∑ i, V.frame.repr x i • V.frame i ∈ V.L0
      rw [V.frame.sum_repr]; exact hx
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
    | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ y ∈ AddSubgroup.closure (GlobalTheory.AdelicLatMove.pureSet Λ), (fun i => (sw D).symm (y i)) ∈ latHat V := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨a, ha, ∑ i, x i • V.frame i, h2 x hx, ?_⟩
        funext i
        rw [V.frame.repr_sum_self]
        rfl
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
      | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
    have := key _ (GlobalTheory.AdelicLatMove.mem_closure_of_mem_hatL Λ _ hz)
    simpa only [RingEquiv.symm_apply_apply] using this

theorem latGHat_one (V : HSp D) : latGHat V 1 = AddSubgroup.closure
    {w | ∃ a ∈ (fun a : D.host.E => (1 : Af D.host.F) ⊗ₜ[D.host.F] a) '' {a | a ∈ D.host.AA}, ∃ z ∈ latHat V, w = a • z} := by
  unfold latGHat gLat
  congr 1
  ext w
  simp only [map_one, Units.val_one, Set.mem_image, Matrix.one_mulVec, exists_eq_right, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, z, hz, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩
    exact ⟨a, ha, z, hz, rfl⟩

theorem map_finHom {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {k : GA D V} {y : GL (Fin V.rank) (SI D)}
    (hy : Formalism.L2.DIV.frGL β y = Lev.finE V k) :
    (finHom V k).val.map (sw D) = β.val * y.val.map (SI D).subtype * (β⁻¹).val :=
  (congrArg Units.val hy).symm

theorem mem_idS_prod (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (s : SI D)
    (hs : ∀ PP ∈ Pg, Formalism.L2.DIV.resS D.host.F PP s = 0) :
    s ∈ Formalism.L2.DIV.idS D.host.F (∏ PP ∈ Pg, PP.asIdeal) := by
  have e : Formalism.L2.DIV.idS D.host.F (∏ PP ∈ Pg, PP.asIdeal) = ∏ PP ∈ Pg, Formalism.L2.DIV.idS D.host.F PP.asIdeal :=
    map_prod (Ideal.mapHom (Formalism.L2.DIV.oToS D.host.F D.host.E)) _ _
  rw [e, Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp only [Ideal.mem_iInf]
    intro PP hP
    have h := hs PP hP
    unfold Formalism.L2.DIV.resS at h
    rw [RingHom.comp_apply] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (RingEquiv.injective _)).1 h)
  · intro P _ Q _ hPQ
    exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ).map (Ideal.mapHom (Formalism.L2.DIV.oToS D.host.F D.host.E))

def fvec (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : La →+ (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddMonoidHom.mk' (fun a => finVec V (ι a)) fun a b => by
    funext i
    simp only [finVec, map_add, Pi.add_apply, TensorProduct.tmul_add]

theorem fvec_smul (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (b : 𝓞 D.host.E) (a : La) :
    fvec V ι (b • a) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • fvec V ι a := by
  funext i
  show (1 : Af D.host.F) ⊗ₜ[D.host.F] (ι (b • a) i) =
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] (ι a i))
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_smul]
  rfl

theorem exists_eq_nsmul {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : M ≠ 0) (x : La) :
    ∀ w ∈ latGHat V 1, fvec V ι x = M • w → ∃ x', x = M • x' := by
  intro w hw e
  have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h1 : finVec V ((M : D.host.E)⁻¹ • ι x) = w := by
    funext i
    have e₁ : (1 : Af D.host.F) ⊗ₜ[D.host.F] (ι x i) = M • w i := congrFun e i
    let j : D.host.E →ₐ[D.host.F] Af D.host.F ⊗[D.host.F] D.host.E := Algebra.TensorProduct.includeRight
    have e₂ : j (ι x i) = j M * w i := by rw [map_natCast, ← nsmul_eq_mul]; exact e₁
    show j ((M : D.host.E)⁻¹ * ι x i) = w i
    rw [map_mul, e₂, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hM', map_one, one_mul]
  obtain ⟨x', hx'⟩ : (M : D.host.E)⁻¹ • ι x ∈ LinearMap.range ι := by
    rw [hι.2, (GlobalTheory.MarkCoset.latG_spec D V 1).1, h1]; exact hw
  refine ⟨x', hι.1 ?_⟩
  rw [map_nsmul, hx', ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hM', one_smul]

theorem mulVec_mem_of_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) {k : GA D V}
    (hk : Lev.finE V k ∈ Formalism.L2.DIV.St β) : ∀ w ∈ latGHat V 1, (finHom V k).val *ᵥ w ∈ latGHat V 1 := by
  obtain ⟨y, hy⟩ := hk
  exact mulVec_mem_of_frame (sw D) (SI D) β (mem_latHat_iff h) (latGHat_one V) _ _ (map_finHom hy)

theorem lift_one_congr {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : V.rank = L.r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} {Mh : Ideal (𝓞 D.host.E)}
    (hM : (∏ PP ∈ L.Pg, PP.asIdeal) * Mh = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V}
    (hp : Lev.finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) (h1 : Formalism.L2.DIV.rTup β L (Lev.finE V k) = 1) :
    ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1, (finHom V k).val *ᵥ fvec V ι a - fvec V ι a = M • w := by
  obtain ⟨y, hy⟩ := Formalism.L2.DIV.parLev_St hp
  have hred : ∀ i j, (y.val - 1) i j ∈ Formalism.L2.DIV.idS D.host.F (∏ PP ∈ L.Pg, PP.asIdeal) := by
    intro i j
    refine mem_idS_prod _ _ fun PP hP => ?_
    have h2 : Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn β PP (Lev.finE V k)) = 1 := congrFun h1 ⟨PP, hP⟩
    have h3 := Formalism.L2.DIV.upper_block_val_submatrix L.hr (Formalism.L2.DIV.blockTri_blkOf_le _ _ (Formalism.L2.DIV.parLev_g hp hP))
    rw [h2, ← hy, Formalism.L2.DIV.redFn_frGL] at h3
    have h4 : (1 : Matrix (Fin L.r) (Fin L.r) (Formalism.L2.DIV.kP PP)) (Fin.cast hL i) (Fin.cast hL j) =
      Formalism.L2.DIV.resS D.host.F PP (y.val i j) := congrFun (congrFun h3 (Fin.cast hL i)) (Fin.cast hL j)
    rw [Matrix.sub_apply, map_sub, ← h4]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, sub_self]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun e => hij (Fin.cast_injective hL e)), map_zero, sub_self]
  intro a ha
  refine Submodule.smul_induction_on ha (fun b hb x _ => ?_) ?_
  · rw [fvec_smul]
    exact mulVec_smul_congr (sw D) (SI D) β (mem_latHat_iff h) (latGHat_one V) _ _ (map_finHom hy)
      (Formalism.L2.DIV.oToS D.host.F D.host.E) hM hred hb _ rfl _
      (((GlobalTheory.MarkCoset.latG_spec D V 1).1 _).1 (hι.2 ▸ LinearMap.mem_range_self ι x))
  · rintro x x' ⟨w, hw, e⟩ ⟨w', hw', e'⟩
    refine ⟨w + w', add_mem hw hw', ?_⟩
    rw [smul_add, ← e, ← e', map_add, Matrix.mulVec_add]
    abel

theorem congr_of_lifts {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : V.rank = L.r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM0 : M ≠ 0) {Mb Mh : Ideal (𝓞 D.host.E)}
    (hMb : Mb = ∏ PP ∈ L.Pg, PP.asIdeal) (hM : Mb * Mh = Ideal.span {(M : 𝓞 D.host.E)}) (hcop : Mb ⊔ Mh = ⊤)
    {G : Type} [Group G] (eG : G →* Formalism.L2.DIV.G0 L.Pg L.r) {lev : G → La →ₗ[𝓞 D.host.E] La}
    (hlev : ∀ g, ∃ κ, Lev.IsLevelLift V β L (eG g) κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (lev g a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w) :
    (∀ a, lev 1 a - a ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La)) ∧
      ∀ g h a, lev (g * h) a - lev g (lev h a) ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La) := by
  choose κ hκ hκ' using hlev
  have hM₁ : (∏ PP ∈ L.Pg, PP.asIdeal) * Mh = Ideal.span {(M : 𝓞 D.host.E)} := by rw [← hMb, hM]
  have hst := fun g => mulVec_mem_of_St hβ (Formalism.L2.DIV.parLev_St (hκ g).2.1)
  refine congr_of_matrices (Q := latGHat V 1) (fvec V ι) M Mb Mh hcop hM lev
    (fun g => (finHom V (κ g)).val) (exists_eq_nsmul hι hM0) hκ' hst ?_ ?_
  · exact lift_one_congr hβ hL hι hM₁ (hκ 1).2.1 ((hκ 1).2.2.trans (map_one eG))
  · intro g h a ha
    have hp : Lev.finE V (κ g * κ h) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
      rw [map_mul]; exact mul_mem (hκ g).2.1 (hκ h).2.1
    have hl : Lev.IsLevelLift V β L (eG (g * h)) (κ g * κ h) := by
      refine ⟨mul_mem (hκ g).1 (hκ h).1, hp, ?_⟩
      rw [map_mul (Lev.finE V), Formalism.L2.DIV.rTup_mul (hκ g).2.1 (hκ h).2.1, (hκ g).2.2, (hκ h).2.2, map_mul]
    have hu := Lev.lift_div_mem hl (hκ (g * h))
    obtain ⟨w, hw, e⟩ := lift_one_congr (L := L) hβ hL hι hM₁ hu.2.1 (Subgroup.mem_bot.1 hu.2.2) a ha
    refine ⟨_, hst g _ (hst h _ hw), ?_⟩
    have e₀ : κ (g * h) = κ g * (κ h * ((κ g * κ h)⁻¹ * κ (g * h))) := by group
    have e₁ : (finHom V (κ (g * h))).val =
        (finHom V (κ g)).val * ((finHom V (κ h)).val * (finHom V ((κ g * κ h)⁻¹ * κ (g * h))).val) := by
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, ← e₀]
    exact mulVec_mul_congr e₁ e

section Record

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem congr_of_levIs {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} (hι : LatEmb (Wc D i) ι)
    (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hMb : l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal)
    {lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La} (hlev : LevIs R i ι l.M (Mfr l) lev) :
    (∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) ∧
      ∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
  congr_of_lifts (L := R.datWp i R.triv) hβ (rank_Wc i) hι (by have := l.three_le; omega) hMb l.prod l.coprime
    R.eG.toMonoidHom hlev

theorem actLev_of_levIs (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} (hι : LatEmb (Wc D i) ι)
    (hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hMb : l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal)
    {lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La} (hlev : LevIs R i ι l.M (Mfr l) lev) :
    ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) :=
  GlobalTheory.LevelActionOfLifts.actLev_of_lifts_of_eq_one D H Dw l Xo c G lev hpq hA (congr_of_levIs R i hι hβ hMb hlev).1 (congr_of_levIs R i hι hβ hMb hlev).2

end Record

theorem actLev_record {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (C : Core D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (i : Fin D.R.m) {Tp : Type} {tup : Tp → T0}
    (O : OMDat C R i Tp tup) {μ₀ t : T0} {I : Ideal (𝓞 D.host.E)}
    {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    (hQ : C.Q.Pins) (hR : R.toLevCh.Is μ₀) (hι : LatEmb (Wc D i) ι) (hh : HalfIs R t C.Q.l.Mb I)
    (hlev : LevIs R i ι C.Q.l.M (Mfr C.Q.l) O.lev) :
    ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2 ∧ ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 := by
  have hpq : 1 ≤ (C.Q.Dw ((i : ℕ) + 1)).p + (C.Q.Dw ((i : ℕ) + 1)).q := by
    have h : (C.Q.Dw ((i : ℕ) + 1)).p = D.R.k + ((i : ℕ) + 1) - 1 := (hQ.2.2.2 _ ⟨Nat.le_add_left _ _, i.2⟩).1
    have := D.R.m_add_three_le_k
    omega
  exact ⟨actLev_of_levIs R i _ _ hpq hQ.2.1.2 hι (hR.βW i) hh.1 hlev,
    actLev_of_levIs R i _ _ hpq hQ.2.1.2 hι (hR.βW i) hh.1 hlev⟩

end GlobalTheory.LevelActionPinned
