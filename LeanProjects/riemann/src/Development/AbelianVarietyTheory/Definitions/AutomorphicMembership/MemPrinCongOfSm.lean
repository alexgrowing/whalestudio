import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.LocalToGlobal.Columns.RecLevelTop

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open GlobalTheory.Mem.Col2.PtExist (mat mat_mulVec mat_symm_mul)
open scoped TensorProduct

namespace GlobalTheory.Mem.ColAd

section Small

variable {k Γ : Type} [Field k] [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ) {n : ℕ}

def Sm (γ : Γ) (A : Matrix (Fin n) (Fin n) k) : Prop := ∀ i j, v (A i j) ≤ γ

variable {v} {γ δ : Γ} {A B : Matrix (Fin n) (Fin n) k}

theorem Sm.add (h : Sm v γ A) (h' : Sm v γ B) : Sm v γ (A + B) := fun i j => Valuation.map_add_le _ (h i j) (h' i j)

theorem Sm.sub (h : Sm v γ A) (h' : Sm v γ B) : Sm v γ (A - B) := fun i j => Valuation.map_sub_le _ (h i j) (h' i j)

theorem Sm.mul (h : Sm v γ A) (h' : Sm v δ B) : Sm v (γ * δ) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_mul' (h i l) (h' l j)

theorem Sm.mono (h : Sm v γ A) (hγ : γ ≤ δ) : Sm v δ A := fun i j => (h i j).trans hγ

theorem sm_one : Sm v 1 (1 : Matrix (Fin n) (Fin n) k) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem Sm.of_sub_one (h : Sm v γ (A - 1)) (hγ : γ ≤ 1) : Sm v 1 A := by
  have := (h.mono hγ).add (sm_one (v := v))
  rwa [sub_add_cancel] at this

theorem Sm.mulVec (h : Sm v γ A) {x : Fin n → k} (hx : ∀ i, v (x i) ≤ δ) (i : Fin n) : v ((A *ᵥ x) i) ≤ γ * δ := by
  simp only [Matrix.mulVec, dotProduct]
  exact Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_mul' (h i l) (hx l)

theorem int_of_mulVec (h : Sm v γ (A - 1)) (hγ : γ < 1) {x : Fin n → k} (hx : ∀ i, v ((A *ᵥ x) i) ≤ 1) (i : Fin n) :
    v (x i) ≤ 1 := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun l => v (x l)) ⟨i, Finset.mem_univ i⟩
  refine (hm i (Finset.mem_univ i)).trans (le_of_not_gt fun hlt => ?_)
  have h1 := h.mulVec (fun l => hm l (Finset.mem_univ l)) m
  have h2 : v (((A - 1) *ᵥ x) m) < v (x m) := h1.trans_lt (mul_lt_of_lt_one_left (zero_lt_one.trans hlt) hγ)
  have h3 : x m = (A *ᵥ x) m - ((A - 1) *ᵥ x) m := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; simp
  have h4 := Valuation.map_sub_lt v ((hx m).trans_lt hlt) h2
  rw [← h3] at h4
  exact lt_irrefl _ h4

end Small

section Near

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "ι" => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)

def dep (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : WithZero (Multiplicative ℤ) := P.valuation E ((qOf P : E) ^ c)

def locM (P : HeightOneSpectrum (𝓞 E)) (x : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E) :=
  (x : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P)

def ratM (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n) : Matrix (Fin n) (Fin n) (P.adicCompletion E) :=
  (mat f).map (algebraMap E (P.adicCompletion E))

variable {P : HeightOneSpectrum (𝓞 E)}

theorem locM_mul (x y : GL (Fin n) (AfE F E)) : locM P (x * y) = locM P x * locM P y := by
  unfold locM
  rw [Units.val_mul, Matrix.map_mul]

theorem locM_one : locM P (1 : GL (Fin n) (AfE F E)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

omit [NumberField E] in

theorem mat_mul (f g : Sp E n ≃ₗ[E] Sp E n) : mat (f * g) = mat f * mat g := by
  ext i j
  rw [Matrix.mul_apply]
  exact (mat_mulVec f (g (Pi.single j 1)) i).symm

theorem ratM_mul (f g : Sp E n ≃ₗ[E] Sp E n) : ratM P (f * g) = ratM P f * ratM P g := by
  unfold ratM
  rw [mat_mul, Matrix.map_mul]

theorem ratM_one : ratM P (1 : Sp E n ≃ₗ[E] Sp E n) = 1 := by
  ext i j
  show algebraMap E _ ((Pi.single j 1 : Sp E n) i) = _
  rw [Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

theorem ratM_mulVec (f : Sp E n ≃ₗ[E] Sp E n) (x : Sp E n) :
    ratM P f *ᵥ (fun i => algebraMap E (P.adicCompletion E) (x i)) = fun i => algebraMap E _ (f x i) := by
  funext i
  rw [← mat_mulVec, map_sum]
  simp [ratM, Matrix.mulVec, dotProduct]

theorem locM_bc (γ : GL (Fin n) E) : locM P (Formalism.UG.bc ι γ) = ratM P (Formalism.UG.glEquiv γ) := by
  refine Matrix.ext fun i j => ?_
  show adAt F P (ι (γ i j)) = algebraMap E _ (Formalism.UG.glEquiv γ (Pi.single j 1) i)
  rw [adAt_inclE]
  simp [Formalism.UG.glEquiv]

theorem dep_ne_zero (c : ℕ) : dep P c ≠ 0 := (Valuation.ne_zero_iff _).2 (pow_ne_zero _ qOf_ne_zero)

theorem val_qOf_lt : P.valuation E (qOf P : E) < 1 := by
  have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).2 (qOf_mem (P := P))
  simpa using this

theorem dep_le_one (c : ℕ) : dep P c ≤ 1 := by
  unfold dep
  rw [map_pow]
  exact pow_le_one' val_qOf_lt.le _

theorem dep_succ_lt (c : ℕ) : dep P (c + 1) < 1 := by
  unfold dep
  rw [map_pow]
  exact pow_lt_one' val_qOf_lt c.succ_ne_zero

theorem dep_succ_le (c : ℕ) : dep P (c + 1) ≤ dep P c := by
  unfold dep
  rw [pow_succ, map_mul]
  exact mul_le_of_le_one_right' val_qOf_lt.le

variable [StarRing E]

theorem mem_stdAt_val {x : Sp E n} : x ∈ stdAt E n P ↔ ∀ i, Valued.v (algebraMap E (P.adicCompletion E) (x i)) ≤ 1 := by
  simp only [mem_stdAt, CharValCompare.intAt_iff, valued_algebraMap]

theorem sm_glint (k : GLint E n P) : Sm Valued.v 1 (ratM P k.1) := fun i j =>
  mem_stdAt_val.1 (glint_mem k (single_mem_stdAt j)) i

theorem mem_prinCong_of_sm {c : ℕ} (k : GLint E n P) (h : Sm Valued.v (dep P c) (ratM P k.1 - 1)) : k ∈ prinCong n P c := by
  intro x hx
  refine mem_stdAt_val.2 fun i => ?_
  have h1 := h.mulVec (mem_stdAt_val.1 hx) i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ratM_mulVec, mul_one, Pi.sub_apply, ← map_sub, valued_algebraMap] at h1
  rw [valued_algebraMap, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  exact (inv_mul_le_one₀ (zero_lt_iff.2 (dep_ne_zero c))).2 h1

theorem exists_frame (x : GL (Fin n) (AfE F E)) (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) :
    ∃ f : Sp E n ≃ₗ[E] Sp E n, CharValCompare.IsFr P (Formalism.UG.CS.globLat x (stdLat E n)) f ∧
      Sm Valued.v (dep P c) (locM P x⁻¹ * ratM P f - 1) := by
  classical
  have hN : Submodule.IsLattice E (Formalism.UG.CS.globLat x (stdLat E n)) := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x
  obtain ⟨f, hf⟩ := CharValCompare.exists_isFr P hN
  have hA : Sm Valued.v 1 (locM P x⁻¹ * ratM P f) := fun i j => by
    have := PtExist.valued_pullV_le x ((hf (Pi.single j 1)).2 (single_mem_stdAt j)) i
    simp only [Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE] at this
    exact this
  have hB : Sm Valued.v 1 (ratM P f⁻¹ * locM P x) := fun i j => by
    refine PtExist.valued_symm_le (u := fun l => (x : Matrix (Fin n) (Fin n) (AfE F E)) l j) hf
      ((PtExist.carries_globLat x _).2 ((mem_latS_std _).2 fun l => ?_)) i
    simp only [Matrix.mulVec, dotProduct]
    rw [← Matrix.mul_apply, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have hAB : locM P x⁻¹ * ratM P f * (ratM P f⁻¹ * locM P x) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (ratM P f), ← ratM_mul, mul_inv_cancel, ratM_one, Matrix.one_mul, ← locM_mul,
      inv_mul_cancel, locM_one]
  have hap : ∀ i j, ∃ y : E, Valued.v (algebraMap E (P.adicCompletion E) y - (ratM P f⁻¹ * locM P x) i j) ≤ dep P (c + 1) := by
    intro i j
    obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small
      (((mat f⁻¹).map ι * (x : Matrix (Fin n) (Fin n) (AfE F E))) i j) {P} (dep_ne_zero (P := P) (c + 1))
    refine ⟨y, ?_⟩
    have e1 : (ratM P f⁻¹ * locM P x) i j = adAt F P (((mat f⁻¹).map ι * (x : Matrix (Fin n) (Fin n) (AfE F E))) i j) := by
      simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, adAt_inclE, ratM, locM]
    rw [e1, e, map_add, adAt_inclE, sub_add_cancel_left, Valuation.map_neg]
    exact (valued_nat_mul_lt hr (hN P (by simp))).le
  choose κ hκ using hap
  let M : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (Matrix.of κ).map (algebraMap E _)
  have h1 : Sm Valued.v (dep P (c + 1)) (M - ratM P f⁻¹ * locM P x) := hκ
  have hM : Sm Valued.v 1 M := by
    have := (h1.mono (dep_le_one _)).add hB
    rwa [sub_add_cancel] at this
  have h2 : Sm Valued.v (dep P (c + 1)) (locM P x⁻¹ * ratM P f * M - 1) := by
    have := hA.mul h1
    rwa [one_mul, Matrix.mul_sub, hAB] at this
  have hv : ∀ w : Sp E n, M *ᵥ (fun i => algebraMap E (P.adicCompletion E) (w i)) =
      fun i => algebraMap E _ ((Matrix.of κ *ᵥ w) i) := fun w => funext fun i => by
    simp [M, Matrix.mulVec, dotProduct]
  have h3 : ∀ w : Sp E n, Matrix.of κ *ᵥ w ∈ stdAt E n P ↔ w ∈ stdAt E n P := fun w => by
    rw [mem_stdAt_val, mem_stdAt_val]
    refine ⟨fun h => int_of_mulVec h2 (dep_succ_lt c) fun i => ?_, fun h i => ?_⟩
    · rw [← Matrix.mulVec_mulVec, hv]
      simpa using hA.mulVec h i
    · have := hM.mulVec h i
      rwa [hv, one_mul] at this
  have hinj : Function.Injective (Matrix.of κ).mulVecLin := by
    refine (injective_iff_map_eq_zero _).2 fun w hw => funext fun i => by_contra fun hi => ?_
    have h4 := mem_stdAt_val.1 ((h3 (((qOf P : E) * w i)⁻¹ • w)).1 (by
      rw [Matrix.mulVec_smul, show Matrix.of κ *ᵥ w = 0 from hw, smul_zero]
      exact zero_mem _)) i
    have hq := qOf_ne_zero (P := P)
    rw [valued_algebraMap, Pi.smul_apply, smul_eq_mul, show ((qOf P : E) * w i)⁻¹ * w i = (qOf P : E)⁻¹ by
      replace hi : w i ≠ 0 := hi
      field_simp, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hq))] at h4
    exact absurd val_qOf_lt (not_lt.2 h4)
  let g : Sp E n ≃ₗ[E] Sp E n := LinearEquiv.ofBijective _ ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  have hg : ratM P g = M := by
    ext i j
    show algebraMap E _ ((Matrix.of κ *ᵥ Pi.single j 1) i) = algebraMap E _ (κ i j)
    simp
  refine ⟨f * g, fun w => (hf (g w)).trans (h3 w), ?_⟩
  rw [ratM_mul, hg, ← Matrix.mul_assoc]
  exact h2.mono (dep_succ_le c)

variable [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

structure Near (c : ℕ) (x : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) : Prop where
  deco : decoRaw ST SG x = p.deco.1
  fr : ∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 x⁻¹ * ratM P.1 (p.fr P) - 1)

variable (hc : CMData F E) {c : ℕ}

theorem exists_near (c : ℕ) {x : GL (Fin n) (AfE F E)} (hx : x ∈ UAd hc n) : ∃ p : DecoF E n ST SG Q, Near c x p := by
  choose f h1 h2 using fun P : Q => exists_frame x P.1 c
  exact ⟨⟨(⟨_, decorated_lattice_exists hc n ST SG x hx⟩, f), h1⟩, rfl, h2⟩

theorem near_one (c : ℕ) : Near c (1 : GL (Fin n) (AfE F E)) (DecoF.base E n ST SG Q) :=
  ⟨decoRaw_one ST SG, fun P i j => by
    rw [inv_one, locM_one, show (DecoF.base E n ST SG Q).fr P = 1 from rfl, ratM_one, Matrix.mul_one, sub_self]
    simp⟩

theorem Near.exists_smul {x : GL (Fin n) (AfE F E)} {p p' : DecoF E n ST SG Q} (h : Near c x p) (h' : Near c x p') :
    ∃ k : GLQ E n Q, (∀ P, k P ∈ prinCong n P.1 c) ∧ p' = ((1, 1, k) : UF E n × GLG E n SG × GLQ E n Q) • p := by
  have hd : p'.deco = p.deco := Subtype.ext (h'.deco.symm.trans h.deco)
  let k : GLQ E n Q := fun P => ⟨(p'.fr P)⁻¹ * p.fr P, fun w => by
    have h1 := p'.2 P (((p'.fr P)⁻¹ * p.fr P) w)
    have h2 : p'.1.2 P (((p'.fr P)⁻¹ * p.fr P) w) = p.1.2 P w := LinearEquiv.apply_symm_apply _ _
    rw [h2, show p'.1.1 = p.1.1 from hd] at h1
    exact h1.symm.trans (p.2 P w)⟩
  refine ⟨k, fun P => mem_prinCong_of_sm _ ?_, Subtype.ext (Prod.ext ?_ (funext fun P => ?_))⟩
  · have h1 := (h.fr P).sub (by simpa using (h'.fr P).mul (sm_glint (k P)))
    have e : ratM P.1 (p.fr P) = ratM P.1 (p'.fr P) * ratM P.1 (k P).1 := by
      rw [← ratM_mul]
      exact congrArg _ (mul_inv_cancel_left _ _).symm
    rw [e] at h1
    convert h1 using 1
    noncomm_ring
  · exact hd.trans (one_smul (UF E n × GLG E n SG) p.1.1).symm
  · show p'.fr P = 1 * p.fr P * ((p'.fr P)⁻¹ * p.fr P)⁻¹
    group

theorem Near.left {x : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : Near c x p) (γ : URat hc n) :
    Near c (Formalism.UG.bc ι (γ : GL (Fin n) E) * x) (((ratHom hc n γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  refine ⟨?_, fun P => ?_⟩
  · have := decoRaw_rawSm hc ST SG γ 1 x
    rw [map_one, OneMemClass.coe_one, inv_one, mul_one, h.deco] at this
    exact this
  · have e : (((ratHom hc n γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p).fr P =
        Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P := by
      show Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P * ((1 : GLint E n P.1)⁻¹).1 = _
      simp
    rw [e, ratM_mul, ← locM_bc (F := F), ← Matrix.mul_assoc, ← locM_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact h.fr P

theorem Near.right {x k : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : Near c x p) (hk : k ∈ K1 hc n ST SG)
    (hQ : ∀ P ∈ Q, Sm Valued.v (dep P c) (locM P k⁻¹ - 1)) : Near c (x * k) p := by
  refine ⟨(decorated_lattice_mul_principal hc n ST SG x hk).trans h.deco, fun P => ?_⟩
  have h1 := ((hQ P.1 P.2).mul ((h.fr P).of_sub_one (dep_le_one c))).add (by simpa using h.fr P)
  rw [mul_one] at h1
  rw [_root_.mul_inv_rev, locM_mul]
  convert h1 using 1
  noncomm_ring

theorem Near.change {x x' : GL (Fin n) (AfE F E)} (hx : x ∈ UAd hc n) (hx' : x' ∈ UAd hc n) {p₀ p : DecoF E n ST SG Q}
    (h : Near c x p₀) (h' : Near c x' p₀) {g : GL (Fin n) (AfE F E)} (hp : Near c (g * x) p) : Near c (g * x') p := by
  have hk := mem_principal_of_same_decoration hc n ST SG hx hx' (h.deco.trans h'.deco.symm)
  have := hp.right hc hk fun P hP => ?_
  · rwa [mul_assoc, mul_inv_cancel_left] at this
  obtain ⟨y, hy, -⟩ := St_one_int (inv_mem (congruence_subgroup_le_stabilizer hc n ST (principal_le_congruence_subgroup hc n ST SG hk)))
  have h0 : Sm Valued.v 1 (locM P (x⁻¹ * x')⁻¹) := fun i j => by
    show Valued.v (adAt F P _) ≤ 1
    rw [hy]
    exact (mem_rInt_iff F E _).1 (y i j).2 P
  have h1 := (h'.fr ⟨P, hP⟩).sub (by simpa only [one_mul] using h0.mul (h.fr ⟨P, hP⟩))
  have e : locM P x'⁻¹ = locM P (x⁻¹ * x')⁻¹ * locM P x⁻¹ := by
    rw [← locM_mul]
    congr 1
    group
  rw [e] at h1
  convert h1 using 1
  noncomm_ring

def CongOne (a : 𝓞 E) (k : GL (Fin n) (AfE F E)) : Prop :=
  ∀ i j, ι (algebraMap (𝓞 E) E a)⁻¹ * ((k : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) ∈
    Formalism.L2.Herm.intAf F E

variable (ST SG Q) in

theorem exists_cong (c : ℕ) : ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ k ∈ UAd hc n, CongOne a k → CongOne a k⁻¹ →
    ∀ (x : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), Near c x p → Near c (x * k) p := by
  classical
  obtain ⟨b, hb0, hb⟩ := rlt_exists_a (ST ∪ SG)
  have hq : ∀ P : HeightOneSpectrum (𝓞 E), ((qOf P : ℕ) : 𝓞 E) ≠ 0 := fun P h => qOf_ne_zero (P := P) (by exact_mod_cast h)
  set a : 𝓞 E := b * ∏ P ∈ Q, ((qOf P : ℕ) : 𝓞 E) ^ c with ha
  have ha0 : a ≠ 0 := mul_ne_zero hb0 (Finset.prod_ne_zero_iff.2 fun P _ => pow_ne_zero _ (hq P))
  have hca : ι (algebraMap (𝓞 E) E a) * ι (algebraMap (𝓞 E) E a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by simpa using ha0), map_one]
  refine ⟨a, ha0, fun k hk h1 h2 x p h => h.right hc ?_ fun P hP i j => ?_⟩
  · refine mem_kOne_of_congruent_one hc n ST SG a (fun P hP => Ideal.mul_mem_right _ _ (hb P (Finset.mem_union_left _ hP)))
      (fun P hP => Ideal.mul_mem_right _ _ (hb P (Finset.mem_union_right _ hP))) hk (fun i j => ⟨_, h1 i j⟩) fun i j => ?_
    show _ = _ + ι (algebraMap (𝓞 E) E a) * (ι (algebraMap (𝓞 E) E a)⁻¹ * _)
    rw [← mul_assoc, hca, one_mul]
    ring
  · have h3 := (mem_rInt_iff F E _).1 (h2 i j) P
    have e : (locM P k⁻¹ - 1) i j = adAt F P (ι (algebraMap (𝓞 E) E a) * (ι (algebraMap (𝓞 E) E a)⁻¹ *
        (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j))) := by
      rw [← mul_assoc, hca, one_mul, map_sub, ← locM_one (F := F)]
      rfl
    rw [e, map_mul, map_mul, adAt_inclE, valued_algebraMap]
    refine (mul_le_of_le_one_right' h3).trans ?_
    obtain ⟨r, hr⟩ : ((qOf P : ℕ) : 𝓞 E) ^ c ∣ a := (Finset.dvd_prod_of_mem _ hP).mul_left _
    rw [hr, map_mul, map_mul, map_pow, map_natCast]
    exact mul_le_of_le_one_right' (HeightOneSpectrum.valuation_le_one (K := E) P r)

variable {hc} in

theorem near_of_isPtOf {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (c : ℕ) : Near c g p := by
  classical
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) p.deco.2.lat.span_eq_top]
    ext w
    refine (h.lat _).symm.trans ?_
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have ok := decorated_lattice_exists hc n ST SG g h.uni
  have hN' : (decoRaw ST SG g).N = p.deco.1.N := hN
  refine ⟨Deco.ext hN (funext fun P => funext fun w => ?_) (funext fun P => funext fun w => ?_), fun P i j => ?_⟩
  · by_cases hw : w ∈ p.deco.1.at P.1
    · obtain ⟨s, hs, h1⟩ := (mem_locP _ _ _).1 hw
      apply mul_left_cancel₀ (mk_ne_zero hs)
      rw [← p.deco.2.f_smul P s w hw, ← ok.f_smul P s w (by rw [Deco.at, hN']; exact hw)]
      refine HasRes.unique ?_ (h.f P _ h1 (lastIdx n) (by have := NeZero.pos n; simp [lastIdx]; omega))
      rw [← hN] at h1
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ h1)]
      exact PtExist.hasRes_redA _ ((mem_globLat g _).1 h1 _)
    · rw [p.deco.2.f_off P w hw, ok.f_off P w (by rw [Deco.at, hN']; exact hw)]
  · by_cases hw : w ∈ p.deco.1.at P.1
    · obtain ⟨s, hs, h1⟩ := (mem_locP _ _ _).1 hw
      funext i
      apply mul_left_cancel₀ (mk_ne_zero hs)
      refine (congrFun (ok.be_smul P s w (by rw [Deco.at, hN']; exact hw)) i).symm.trans
        (Eq.trans ?_ (congrFun (p.deco.2.be_smul P s w hw) i))
      refine HasRes.unique ?_ (h.be P _ h1 i)
      rw [← hN] at h1
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ h1)]
      exact PtExist.hasRes_redA _ ((mem_globLat g _).1 h1 _)
    · rw [p.deco.2.be_off P w hw, ok.be_off P w (by rw [Deco.at, hN']; exact hw)]
  · have e : ratM P.1 (p.fr P) = locM P.1 g := Matrix.ext fun i j => (h.fr P i j).symm
    rw [e, ← locM_mul, inv_mul_cancel, locM_one, sub_self]
    simp

variable (ST SG Q) in

def ptOf (c : ℕ) (x : GL (Fin n) (AfE F E)) : DecoF E n ST SG Q := Classical.epsilon (Near c x)

theorem near_ptOf (c : ℕ) {x : GL (Fin n) (AfE F E)} (hx : x ∈ UAd hc n) : Near c x (ptOf ST SG Q c x) :=
  Classical.epsilon_spec (exists_near hc c hx)

end Near

end GlobalTheory.Mem.ColAd

end
