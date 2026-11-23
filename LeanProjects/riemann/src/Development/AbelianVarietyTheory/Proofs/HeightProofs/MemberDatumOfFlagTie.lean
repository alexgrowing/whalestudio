import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.BesselDatum
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BesselPeriodPositionOneEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData
open scoped TensorProduct

namespace GlobalTheory.BesselCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def co (B : HSp D) (v : B.V) : Fin B.rank → D.host.E := fun k => B.frame.repr v k

def eMat (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) : Matrix (Fin B.rank) (Fin ρ) D.host.E := fun k i => B.frame.repr (e i) k

theorem co_surj (B : HSp D) (x : Fin B.rank → D.host.E) : ∃ v, co B v = x :=
  ⟨B.frame.equivFun.symm x, by
    funext k; unfold co; rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩

theorem eMat_surj (B : HSp D) {ρ : ℕ} (M : Matrix (Fin B.rank) (Fin ρ) D.host.E) : ∃ e, eMat B e = M := by
  choose e he using fun i => co_surj B (fun k => M k i)
  exact ⟨e, by funext k i; exact congrFun (he i) k⟩

theorem sig_eq (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, incA, sigR, inclR]
  rfl

theorem hT_co (B : HSp D) (x y : B.V) :
    B.hT x y = ∑ i, ∑ j, star (co B x i) * B.gram i j * co B y j := by
  conv_lhs => rw [← B.frame.sum_repr x, ← B.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [co, HSpace.gram, RingHom.id_apply, starRingEnd_apply]
  ring

theorem cT_mulVec (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (v : B.V) (i : Fin ρ) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (eMat B e) * B.gram).mulVec (co B v) i = B.hT (e i) v := by
  rw [hT_co, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, sig_eq]
  rfl

theorem cT_mul (B : HSp D) {ρ ρ' : ℕ} (e : Fin ρ → B.V) (e' : Fin ρ' → B.V) (i j) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (eMat B e) * B.gram * eMat B e') i j = B.hT (e i) (e' j) := by
  rw [← cT_mulVec]; rfl

theorem frameMat_eq (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : frameMat B A ι = eMat B (fun i => ι (A.frame i)) := by
  funext k i; simp [frameMat, eMat, LinearMap.toMatrix_apply]

theorem hform_co (B : HSp D) (x y : B.V) :
    Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram (co B x) (co B y) = B.hT x y := by
  rw [hT_co]; rfl

theorem hA_vec (B : HSp D) (x y : B.V) : hA B (vecA B x) (vecA B y) = incA D (B.hD x y) := by
  unfold HSpace.hD
  rw [hT_co]
  simp only [hA, vecA, map_sum, map_mul, cA_inc, co]

theorem hA_add (B : HSp D) (x x' y) : hA B (x + x') y = hA B x y + hA B x' y := by
  simp only [hA, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_smul (B : HSp D) (a : AE D) (x y) : hA B (a • x) y = a * hA B x y := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_smul_right (B : HSp D) (a : AE D) (x y) : hA B x (a • y) = cA D a * hA B x y := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_sum (B : HSp D) {ρ : ℕ} (x : Fin ρ → Fin B.rank → AE D) (y) : hA B (∑ l, x l) y = ∑ l, hA B (x l) y := by
  classical
  have : ∀ s : Finset (Fin ρ), hA B (∑ l ∈ s, x l) y = ∑ l ∈ s, hA B (x l) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hA]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add, ih]
  exact this _

theorem vecA_smul (B : HSp D) (t : D.host.E) (v : B.V) : vecA B (t • v) = incA D t • vecA B v := by
  funext k; simp [vecA]

theorem actV_smul (B : HSp D) (n : GA D B) (t : D.host.E) (v : B.V) : actV B n (t • v) = incA D t • actV B n v := by
  unfold actV; rw [vecA_smul, Matrix.mulVec_smul]

theorem eMat_mulVec (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (a : Fin ρ → AE D) :
    ((eMat B e).map (incA D)).mulVec a = ∑ l, a l • vecA B (e l) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, eMat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecA]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem subOne_iff (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (n : GA D B) (v : B.V) (a : Fin ρ → AE D) :
    (subOne B n).mulVec (ratV (co B v)) = ((eMat B e).map (incA D)).mulVec a ↔
      actV B n v = vecA B v + ∑ l, a l • vecA B (e l) := by
  rw [eMat_mulVec]
  unfold subOne
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add']
  rfl

def NS (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) : Set (GA D B) :=
  {n | (∀ i, ∃ c : Fin ρ → AE D, (∀ l, i ≤ l → c l = 0) ∧
        actV B n (e i) = vecA B (e i) + ∑ l, c l • vecA B (e l)) ∧
    ∀ x : B.V, (∀ i, B.hD x (e i) = 0) →
      ∃ c : Fin ρ → AE D, actV B n x = vecA B x + ∑ l, c l • vecA B (e l)}

theorem NFlag_eMat (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) : NFlag B (eMat B e) = Subgroup.closure (NS B e) := by
  unfold NFlag
  congr 1
  ext g
  refine and_congr (forall_congr' fun i => exists_congr fun a => and_congr Iff.rfl (subOne_iff B e g (e i) a)) ?_
  constructor
  · intro h x hx
    obtain ⟨a, ha⟩ := h (co B x) (by funext i; rw [cT_mulVec]; exact hx i)
    exact ⟨a, (subOne_iff B e g x a).1 ha⟩
  · intro h x hx
    obtain ⟨v, rfl⟩ := co_surj B x
    obtain ⟨a, ha⟩ := h v (fun i => by have := congrFun hx i; rwa [cT_mulVec] at this)
    exact ⟨a, (subOne_iff B e g v a).2 ha⟩

theorem NS_smul_le (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (t : Fin ρ → D.host.E) (ht : ∀ i, t i ≠ 0) :
    NS B e ⊆ NS B (fun i => t i • e i) := by
  have key : ∀ (s : D.host.E) (c : Fin ρ → AE D), incA D s • ∑ l, c l • vecA B (e l) =
      ∑ l, (incA D (s * (t l)⁻¹) * c l) • vecA B (t l • e l) := by
    intro s c
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [vecA_smul, smul_smul, smul_smul]
    congr 1
    rw [mul_right_comm, ← map_mul, mul_assoc, inv_mul_cancel₀ (ht l), mul_one]
  rintro n ⟨h1, h2⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, h⟩ := h1 i
    refine ⟨fun l => incA D (t i * (t l)⁻¹) * c l, fun l hl => by simp [hc l hl], ?_⟩
    rw [actV_smul, h, smul_add, key, vecA_smul]
  · obtain ⟨c, h⟩ := h2 x (fun i => by
      have := hx i
      unfold HSpace.hD at this ⊢
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_zero] at this
      exact this.resolve_left (by simpa using ht i))
    refine ⟨fun l => incA D (1 * (t l)⁻¹) * c l, ?_⟩
    rw [h, ← key, map_one, one_smul]

theorem NS_smul (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (t : Fin ρ → D.host.E) (ht : ∀ i, t i ≠ 0) :
    NS B (fun i => t i • e i) = NS B e := by
  refine subset_antisymm ?_ (NS_smul_le B e t ht)
  have := NS_smul_le B (fun i => t i • e i) (fun i => (t i)⁻¹) (fun i => inv_ne_zero (ht i))
  simpa [smul_smul, ht] using this

def spanA (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) : Submodule (AE D) (Fin B.rank → AE D) :=
  Submodule.span (AE D) (Set.range fun l => vecA B (e l))

theorem mt_mul (B : HSp D) (g h : GA D B) : mt B (g * h) = mt B g * mt B h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (B : HSp D) : mt B 1 = 1 := by simp [Formalism.L2.Theta.mt]

set_option maxHeartbeats 1000000 in

theorem closure_prop (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (n : GA D B) (hn : n ∈ Subgroup.closure (NS B e)) :
    (∀ s ∈ spanA B e, (mt B n).mulVec s ∈ spanA B e) ∧
      ∀ x : B.V, (∀ i, B.hD x (e i) = 0) → actV B n x - vecA B x ∈ spanA B e := by
  have hmem : ∀ c : Fin ρ → AE D, ∑ l, c l • vecA B (e l) ∈ spanA B e := fun c =>
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hgen : ∀ l, vecA B (e l) ∈ spanA B e := fun l => Submodule.subset_span ⟨l, rfl⟩
  have ext : ∀ M : Matrix (Fin B.rank) (Fin B.rank) (AE D), (∀ l, M.mulVec (vecA B (e l)) ∈ spanA B e) →
      ∀ s ∈ spanA B e, M.mulVec s ∈ spanA B e := by
    intro M hM s hs
    have : spanA B e ≤ (spanA B e).comap M.mulVecLin := Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact hM l)
    exact this hs
  induction hn using Subgroup.closure_induction'' with
  | one => exact ⟨fun s hs => by rwa [mt_one, Matrix.one_mulVec], fun x _ => by simp [actV, mt_one]⟩
  | mem g hg =>
    refine ⟨ext _ fun l => ?_, fun x hx => ?_⟩
    · obtain ⟨c, -, h⟩ := hg.1 l
      have h' : (mt B g).mulVec (vecA B (e l)) = _ := h
      rw [h']; exact add_mem (hgen l) (hmem c)
    · obtain ⟨c, h⟩ := hg.2 x hx
      rw [h, add_sub_cancel_left]; exact hmem c
  | inv_mem g hg =>
    have hinv : ∀ v, (mt B g⁻¹).mulVec ((mt B g).mulVec v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mulVec]
    have h1 : ∀ l, (mt B g⁻¹).mulVec (vecA B (e l)) ∈ spanA B e := by
      intro l
      induction l using WellFoundedLT.induction with
      | ind l ih =>
        obtain ⟨c, hc, h⟩ := hg.1 l
        have h2 := hinv (vecA B (e l))
        have h' : (mt B g).mulVec (vecA B (e l)) = _ := h
        rw [h', Matrix.mulVec_add, ← eq_sub_iff_add_eq] at h2
        rw [h2]
        refine sub_mem (hgen l) ?_
        rw [← Matrix.mulVecLin_apply, map_sum]
        refine Submodule.sum_mem _ fun k _ => ?_
        rcases lt_or_ge k l with hk | hk
        · rw [map_smul]; exact Submodule.smul_mem _ _ (ih k hk)
        · simp [hc k hk]
    refine ⟨ext _ h1, fun x hx => ?_⟩
    obtain ⟨c, h⟩ := hg.2 x hx
    have h2 := hinv (vecA B x)
    have h' : (mt B g).mulVec (vecA B x) = _ := h
    rw [h', Matrix.mulVec_add, ← eq_sub_iff_add_eq] at h2
    unfold actV
    rw [h2, sub_sub_cancel_left]
    exact neg_mem (ext _ h1 _ (hmem c))
  | mul g h _ _ ihg ihh =>
    refine ⟨fun s hs => ?_, fun x hx => ?_⟩
    · rw [mt_mul, ← Matrix.mulVec_mulVec]; exact ihg.1 _ (ihh.1 s hs)
    · have := add_mem (ihg.1 _ (ihh.2 x hx)) (ihg.2 x hx)
      have e1 : (mt B g).mulVec (actV B h x - vecA B x) = actV B (g * h) x - actV B g x := by
        rw [Matrix.mulVec_sub]
        unfold actV
        rw [mt_mul, ← Matrix.mulVec_mulVec]
      rwa [e1, sub_add_sub_cancel] at this

def valOf (ψ : AddChar (AF D.host.F) ℂ) (B : HSp D) {ρ : ℕ} (e f : Fin ρ → B.V) (z : B.V) (c : Fin ρ → D.host.E)
    (n : GA D B) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D)
    (∑ i : Fin ρ, incA D (c i) * hA B (actV B n (Fin.snoc (α := fun _ => B.V) e z i.succ)) (vecA B (f i))))

theorem hA_coeff (B : HSp D) {ρ : ℕ} (e f : Fin ρ → B.V) (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0)
    (a : Fin ρ → AE D) (i : Fin ρ) : hA B (∑ l, a l • vecA B (e l)) (vecA B (f i)) = a i := by
  rw [hA_sum]
  simp only [hA_smul, hA_vec, ef]
  rw [Finset.sum_eq_single i] <;> simp +contextual

theorem isBesVal_unique (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (b : BesDat A B ι)
    (e f : Fin b.ρ → B.V) (z : B.V) (he : b.e = eMat B e) (hz : b.z = co B z)
    (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) (zf : ∀ i, B.hD z (f i) = 0) (n : GA D B) (v : ℂ)
    (hv : IsBesVal ψ b n v) : v = valOf ψ B e f z b.c n := by
  obtain ⟨a, a', h1, h2, rfl⟩ := hv
  rw [he] at h1 h2
  rw [hz] at h2
  have h1' := fun i => (subOne_iff B e n (e i) (a i)).1 (h1 i)
  have h2' := (subOne_iff B e n z a').1 h2
  unfold valOf
  congr 2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.1 + 1 = b.ρ
  · have : i.succ = Fin.last b.ρ := Fin.ext hi
    rw [this, Fin.snoc_last, h2', hA_add, hA_coeff B e f ef, hA_vec, zf, if_pos hi, Finset.sum_eq_zero]
    · rw [map_zero, zero_add, zero_add]
    · intro j _
      have := j.2
      rw [if_neg (by omega)]
  · have hlt : i.1 + 1 < b.ρ := by have := i.2; omega
    have : i.succ = Fin.castSucc (⟨i.1 + 1, hlt⟩ : Fin b.ρ) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc, h1', hA_add, hA_coeff B e f ef, hA_vec, ef, if_neg hi,
      if_neg (fun h => by have : i.1 + 1 = i.1 := congrArg Fin.val h; omega), Finset.sum_eq_single (⟨i.1 + 1, hlt⟩ : Fin b.ρ)]
    · rw [if_pos rfl, map_zero, zero_add, add_zero]
    · intro j _ hj
      rw [if_neg (fun h => hj (Fin.ext h))]
    · exact fun h => absurd (Finset.mem_univ _) h

theorem besChar_eq_valOf (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (b : BesDat A B ι)
    (e f : Fin b.ρ → B.V) (z : B.V) (he : b.e = eMat B e) (hz : b.z = co B z)
    (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) (zf : ∀ i, B.hD z (f i) = 0)
    (n : GA D B) (hn : n ∈ NFlag B b.e) : besChar ψ b n = valOf ψ B e f z b.c n := by
  have hze : ∀ i, B.hD z (e i) = 0 := fun i => by
    have := congrFun b.z_perpE i
    rwa [he, hz, cT_mulVec] at this
  have hee : ∀ j i, B.hD (e j) (e i) = 0 := fun j i => by
    have := congrFun (congrFun b.e_iso.2 i) j
    rwa [he, cT_mul] at this
  rw [he, NFlag_eMat] at hn
  have key : ∀ x, (∀ i, B.hD x (e i) = 0) →
      ∃ a, (subOne B n).mulVec (ratV (co B x)) = ((eMat B e).map (incA D)).mulVec a := by
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ((closure_prop B e n hn).2 x hx)
    exact ⟨a, (subOne_iff B e n x a).2 (by rw [ha, add_sub_cancel])⟩
  have hex : ∃ v, IsBesVal ψ b n v := by
    choose a ha using fun j => key (e j) (hee j)
    obtain ⟨a', ha'⟩ := key z hze
    refine ⟨_, a, a', ?_, ?_, rfl⟩
    · rw [he]; exact ha
    · rw [he, hz]; exact ha'
  unfold besChar
  rw [dif_pos hex]
  exact isBesVal_unique ψ b e f z he hz ef zf n _ hex.choose_spec

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem N_eq (d : BesselDatum A B ι) : d.N = Subgroup.closure (NS B d.e) := rfl

theorem psiN_eq_valOf (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (n : GA D B) :
    d.psiN ψ n = valOf ψ B d.e d.f d.z (fun _ => d.θ) n := by
  unfold BesselDatum.psiN valOf BesselDatum.simpleSum
  rw [Finset.mul_sum]; rfl

theorem hD_swap_zero {x y : B.V} (h : B.hD x y = 0) : B.hD y x = 0 := by
  have := hT_swap (S := B) h
  rwa [star_zero] at this

def toBes (d : BesselDatum A B ι) : BesDat A B ι where
  ρ := d.ρ
  codim := by rw [d.rank_eq]; omega
  e := eMat B d.e
  e_iso := by
    refine ⟨?_, ?_⟩
    · refine (Fintype.linearIndependent_iff (v := fun i k => eMat B d.e k i)).2 ?_
      intro g hg i
      have h0 : ∑ l, g l • d.e l = 0 := by
        apply B.frame.repr.injective
        refine Finsupp.ext fun k => ?_
        have := congrFun hg k
        simpa [eMat, Finset.sum_apply] using this
      have h1 : B.hT (d.f i) (∑ l, g l • d.e l) = 0 := by rw [h0, map_zero]
      have ef : ∀ l, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun l => d.ef l i
      simpa [map_sum, ef] using h1
    · funext i j; rw [cT_mul]; exact d.ee j i
  e_perp := by funext i j; rw [frameMat_eq, cT_mul]; exact d.eA j _
  z := co B d.z
  z_perpA := by funext i; rw [frameMat_eq, cT_mulVec]; exact d.zA _
  z_perpE := by funext i; rw [cT_mulVec]; exact hD_swap_zero (d.ez i)
  z_ne := by rw [hform_co]; exact d.zz
  c := fun _ => d.θ
  c_ne := fun _ => d.θ_ne
  y := 1

def Same (b : BesDat A B ι) (d : BesselDatum A B ι) : Prop :=
  b.ρ = d.ρ ∧ b.z = co B d.z ∧ NFlag B b.e = d.N ∧ ∀ ψ, ∀ n ∈ d.N, besChar ψ b n = d.psiN ψ n

theorem same_toBes (d : BesselDatum A B ι) : Same (toBes d) d := by
  have hN : NFlag B (toBes d).e = d.N := NFlag_eMat B d.e
  refine ⟨rfl, rfl, hN, fun ψ n hn => ?_⟩
  rw [psiN_eq_valOf]
  exact besChar_eq_valOf ψ (toBes d) d.e d.f d.z rfl rfl d.ef (fun i => hD_swap_zero (d.fz i)) n (hN ▸ hn)

def ClauseFlag (ψ : AddChar (AF D.host.F) ℂ) (b : BesDat A B ι) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) (C a : ℂ) : Prop :=
  ∀ (μN : Measure (NFlag B b.e)) (𝓕N : Set (NFlag B b.e)), μN.IsHaarMeasure →
    IsFundamentalDomain (NFlagQ B b.e) 𝓕N μN → μN 𝓕N = 1 →
    a = C * ∫ h in 𝓕, ∫ n in 𝓕N, star (φ h) * F ((n : GA D B) * s h * (b.y : GA D B)) *
      star (besChar ψ b (n : GA D B)) ∂μN ∂μ

def ClauseDual (ψ : AddChar (AF D.host.F) ℂ) (d : BesselDatum A B ι) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) (C a : ℂ) : Prop :=
  ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → a = C * d.period ψ μ 𝓕 ν 𝓝 s (fun g => star (φ g)) F

def ClauseOn (H : Subgroup (GA D B)) (χ : GA D B → ℂ) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) (C a : ℂ) : Prop :=
  ∀ (ν : Measure H) (𝓝 : Set H), ν.IsHaarMeasure → IsFundamentalDomain ((GQ B).subgroupOf H) 𝓝 ν → ν 𝓝 = 1 →
    a = C * ∫ h in 𝓕, star (φ h) * ∫ n in 𝓝, F ((n : GA D B) * s h) * star (χ n) ∂ν ∂μ

theorem clauseOn_congr {H H' : Subgroup (GA D B)} {χ χ' : GA D B → ℂ} (h : H = H') (hχ : ∀ n ∈ H', χ n = χ' n)
    (μ : Measure (GA D A)) (𝓕 s φ F C a) : ClauseOn H χ μ 𝓕 s φ F C a ↔ ClauseOn H' χ' μ 𝓕 s φ F C a := by
  subst h
  have : ∀ n : H, χ n = χ' n := fun n => hχ n n.2
  simp only [ClauseOn, this]

theorem clause_iff {b : BesDat A B ι} {d : BesselDatum A B ι} (h : Same b d) (hy : (b.y : GA D B) = 1)
    (ψ μ 𝓕 s φ F C a) : ClauseFlag ψ b μ 𝓕 s φ F C a ↔ ClauseDual ψ d μ 𝓕 s φ F C a := by
  have h1 : ClauseFlag ψ b μ 𝓕 s φ F C a ↔ ClauseOn (NFlag B b.e) (besChar ψ b) μ 𝓕 s φ F C a := by
    unfold ClauseFlag ClauseOn
    simp only [hy, mul_one, mul_assoc, integral_const_mul]
    rfl
  have h2 : ClauseDual ψ d μ 𝓕 s φ F C a ↔ ClauseOn d.N (d.psiN ψ) μ 𝓕 s φ F C a :=
    ⟨fun H ν 𝓝 h1 h2 h3 => H ν 𝓝 ⟨h1, h2, h3⟩, fun H ν 𝓝 h => H ν 𝓝 h.1 h.2.1 h.2.2⟩
  rw [h1, h2]
  exact clauseOn_congr h.2.2.1 (h.2.2.2 ψ) ..

theorem gram_isUnit (B : HSp D) : IsUnit B.gram := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  refine (injective_iff_map_eq_zero B.gram.mulVecLin).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := co_surj B x
  have hv : v = 0 := by
    refine B.nondeg.2 v fun y => ?_
    rw [hT_co]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun hx i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simp only [mul_assoc, ← Finset.mul_sum, this, mul_zero]
  subst hv; funext k; simp [co]

theorem exists_rep (B : HSp D) (l : B.V →ₗ[D.host.E] D.host.E) : ∃ v, ∀ x, B.hT v x = l x := by
  obtain ⟨w, hw⟩ := (Matrix.vecMul_surjective_iff_isUnit.2 (gram_isUnit B)) (fun j => l (B.frame j))
  obtain ⟨v, hv⟩ := co_surj B (fun i => star (w i))
  refine ⟨v, fun x => ?_⟩
  rw [hT_co, hv, Finset.sum_comm]
  conv_rhs => rw [← B.frame.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrFun hw j
  simp only [Matrix.vecMul, dotProduct] at this
  rw [← Finset.sum_mul, map_smul, smul_eq_mul, ← this, mul_comm]
  simp [co]

theorem exists_dual (hι : HSpace.IsIsomEmb A B ι) {ρ : ℕ} (e : Fin ρ → B.V) (z : B.V)
    (hli : LinearIndependent D.host.E e) (ee : ∀ i j, B.hT (e i) (e j) = 0) (eA : ∀ i x, B.hT (ι x) (e i) = 0)
    (ez : ∀ i, B.hT z (e i) = 0) (zA : ∀ x, B.hT z (ι x) = 0) (zz : B.hT z z ≠ 0) :
    ∃ f : Fin ρ → B.V, (∀ i j, B.hT (f i) (f j) = 0) ∧ (∀ i j, B.hT (f j) (e i) = if i = j then 1 else 0) ∧
      (∀ i x, B.hT (f i) (ι x) = 0) ∧ ∀ i, B.hT (f i) z = 0 := by
  have sw : ∀ x y : B.V, B.hT y x = star (B.hT x y) := fun x y => hT_swap rfl
  have h1 : ∀ j, ∃ g : B.V, (∀ i, B.hT g (e i) = if i = j then 1 else 0) ∧ (∀ x, B.hT g (ι x) = 0) ∧ B.hT g z = 0 := by
    intro j
    obtain ⟨l, hl⟩ := LinearMap.exists_extend ((Finsupp.lapply j).comp hli.repr)
    have hl' : ∀ i, l (e i) = if i = j then 1 else 0 := fun i => by
      have := LinearMap.congr_fun hl ⟨e i, Submodule.subset_span ⟨i, rfl⟩⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at this
      rw [this, hli.repr_eq_single i _ rfl, Finsupp.single_apply]
    obtain ⟨v, hv⟩ := exists_rep B l
    obtain ⟨w, hw⟩ := exists_rep A (l.comp ι)
    have zA' : ∀ x, B.hT (ι x) z = 0 := fun x => by rw [sw, zA, star_zero]
    refine ⟨v - ι w - star (l z / B.hT z z) • z, fun i => ?_, fun x => ?_, ?_⟩
    · simp [hv, hl', eA, ez]
    · simp [hv, hι w x, hw, zA]
    · simp [hv, zA', zz, starRingEnd_apply]
  choose g hge hgA hgz using h1
  have heg : ∀ i j, B.hT (e i) (g j) = if i = j then 1 else 0 := fun i j => by
    rw [sw, hge]; split_ifs <;> simp
  have eA' : ∀ i x, B.hT (e i) (ι x) = 0 := fun i x => by rw [sw, eA, star_zero]
  have ez' : ∀ i, B.hT (e i) z = 0 := fun i => by rw [sw, ez, star_zero]
  refine ⟨fun j => g j - ∑ l, ((1 / 2 : D.host.E) * B.hT (g l) (g j)) • e l, fun i j => ?_, fun i j => ?_,
    fun i x => ?_, fun i => ?_⟩
  · have h2 : star (2 : D.host.E) = 2 := by simp
    simp [map_sum, LinearMap.sum_apply, hge, heg, ee, starRingEnd_apply, ← sw, h2]
    ring
  · simp [map_sum, LinearMap.sum_apply, hge, ee]
  · simp [map_sum, LinearMap.sum_apply, hgA, eA']
  · simp [map_sum, LinearMap.sum_apply, hgz, ez']

theorem exists_same (hι : HSpace.IsIsomEmb A B ι) (b : BesDat A B ι) (θ : D.host.E) (hθ : θ ≠ 0) :
    ∃ d : BesselDatum A B ι, d.θ = θ ∧ Same b d := by
  have sw : ∀ x y : B.V, B.hT y x = star (B.hT x y) := fun x y => hT_swap rfl
  obtain ⟨e, he⟩ := eMat_surj B b.e
  obtain ⟨z, hz⟩ := co_surj B b.z
  have ee : ∀ i j, B.hT (e i) (e j) = 0 := fun i j => by
    have := congrFun (congrFun b.e_iso.2 i) j
    rwa [← he, cT_mul] at this
  have ext : ∀ v : B.V, (∀ k, B.hT (ι (A.frame k)) v = 0) → ∀ x, B.hT (ι x) v = 0 := fun v hv x => by
    rw [← A.frame.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hv, smul_zero,
      Finset.sum_const_zero]
  have eA : ∀ i x, B.hT (ι x) (e i) = 0 := fun i => ext _ fun k => by
    have := congrFun (congrFun b.e_perp k) i
    rwa [← he, frameMat_eq, cT_mul] at this
  have zA : ∀ x, B.hT (ι x) z = 0 := ext _ fun k => by
    have := congrFun b.z_perpA k
    rwa [← hz, frameMat_eq, cT_mulVec] at this
  have ez : ∀ i, B.hT (e i) z = 0 := fun i => by
    have := congrFun b.z_perpE i
    rwa [← hz, ← he, cT_mulVec] at this
  have zz : B.hT z z ≠ 0 := by have := b.z_ne; rwa [← hz, hform_co] at this
  have hli : LinearIndependent D.host.E e := by
    have h := b.e_iso.1
    rw [← he] at h
    exact LinearIndependent.of_comp B.frame.equivFun.toLinearMap h
  obtain ⟨f, ff, fe, fA, fz⟩ := exists_dual hι e z hli ee eA (fun i => by rw [sw, ez, star_zero])
    (fun x => by rw [sw, zA, star_zero]) zz
  let t : ℕ → D.host.E := fun k => ∏ l : Fin b.ρ, if k ≤ l.1 then θ / b.c l else 1
  have ht : ∀ k, t k ≠ 0 := fun k => Finset.prod_ne_zero_iff.2 fun l _ => by
    split_ifs
    · exact div_ne_zero hθ (b.c_ne l)
    · exact one_ne_zero
  have htop : t b.ρ = 1 := Finset.prod_eq_one fun l _ => if_neg (by have := l.2; omega)
  have hstep : ∀ i : Fin b.ρ, t i = θ / b.c i * t (i + 1) := fun i => by
    simp only [t]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      if_pos le_rfl, if_neg (by omega), one_mul]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    have : l.1 ≠ i.1 := fun h => (Finset.mem_erase.1 hl).1 (Fin.ext h)
    exact if_congr (by omega) rfl rfl
  let d : BesselDatum A B ι :=
    { isom := hι
      ρ := b.ρ
      rank_eq := by have := b.codim; omega
      e := fun i => t i • e i
      f := fun i => (star (t i))⁻¹ • f i
      z := z
      ee := fun i j => by simp [HSpace.hD, ee]
      ff := fun i j => by simp [HSpace.hD, ff]
      ef := fun i j => by
        simp only [HSpace.hD, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, fe, smul_eq_mul, RingHom.id_apply,
          starRingEnd_apply, star_inv₀, star_star]
        split_ifs with h
        · subst h; simp [ht]
        · simp
      eA := fun i x => by simp [HSpace.hD, eA]
      fA := fun i x => by
        have : B.hT (ι x) (f i) = 0 := by rw [sw, fA, star_zero]
        simp [HSpace.hD, this]
      zA := zA
      ez := fun i => by
        have : B.hT z (e i) = 0 := by rw [sw, ez, star_zero]
        simp [HSpace.hD, this]
      fz := fun i => by
        have : B.hT z (f i) = 0 := by rw [sw, fz, star_zero]
        simp [HSpace.hD, this]
      zz := zz
      θ := θ
      θ_ne := hθ }
  have hN : NFlag B b.e = d.N := by
    rw [N_eq, ← he, NFlag_eMat]
    exact congrArg Subgroup.closure (NS_smul B e (fun i => t i) (fun i => ht i)).symm
  refine ⟨d, rfl, rfl, hz.symm, hN, fun ψ n hn => ?_⟩
  rw [besChar_eq_valOf ψ b e f z he.symm hz.symm fe fz n (hN ▸ hn), psiN_eq_valOf]
  unfold valOf
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  have haux : ∀ k : Fin (b.ρ + 1), Fin.snoc (α := fun _ => B.V) (fun i : Fin b.ρ => t i • e i) z k =
      t k • Fin.snoc (α := fun _ => B.V) e z k := fun k => by
    induction k using Fin.lastCases with
    | last => simp [htop]
    | cast k => simp
  show _ = incA D θ * hA B (actV B n (Fin.snoc (α := fun _ => B.V) (fun i : Fin b.ρ => t i • e i) z i.succ))
    (vecA B ((star (t i))⁻¹ • f i))
  rw [haux, actV_smul, vecA_smul, hA_smul, hA_smul_right, cA_inc, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  congr 2
  have h1 := ht (i + 1)
  have h2 := b.c_ne i
  rw [star_inv₀, star_star, hstep i, Fin.val_succ]
  field_simp

section Ties

open GlobalTheory.BesselGap

variable {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T}
  {piT : D.what₂.Word → 𝓞 D.host.E} {piG : Fin 2 → 𝓞 D.host.E}

def negDatum (d : BesselDatum A B ι) : BesselDatum A B (-ι) :=
  { d with
    isom := fun x y => by simpa using d.isom x y
    eA := fun i x => by simpa [HSpace.hD] using d.eA i x
    fA := fun i x => by simpa [HSpace.hD] using d.fA i x
    zA := fun x => by simpa [HSpace.hD] using d.zA x }

def oneSym (X : ThetaX D) (u₁ : D.what₂.Word) : ThetaX D := { X with posSym := fun _ => X.posSym u₁ }

def oneSymT (T : ThetaTied D X) (u₁) : ThetaTied D (oneSym X u₁) := { T with }

def oneSymW (Wl : WeilTied D X T) (u₁) : WeilTied D (oneSym X u₁) (oneSymT T u₁) :=
  { Wl with om_tw := ⟨Wl.om_tw.1, Wl.om_tw.2, Wl.om_tw.3, Wl.om_tw.4⟩ }

end Ties

theorem isAniso_iff (A : HSp D) : IsAniso A ↔ ∀ v : A.V, A.hD v v = 0 → v = 0 := by
  constructor
  · intro h v hv
    by_contra hne
    refine h 1 (eMat A fun _ => v) ⟨one_pos, ?_, ?_⟩
    · refine (linearIndependent_unique_iff (v := fun (_ : Fin 1) k => A.frame.repr v k)).2 fun h0 => hne ?_
      apply A.frame.repr.injective
      refine Finsupp.ext fun k => ?_
      simpa using congrFun h0 k
    · funext i j; rw [cT_mul]; exact hv
  · rintro h r C ⟨hr, hli, hC⟩
    obtain ⟨e, rfl⟩ := eMat_surj A C
    have h1 := congrFun (congrFun hC ⟨0, hr⟩) ⟨0, hr⟩
    rw [cT_mul] at h1
    refine hli.ne_zero ⟨0, hr⟩ ?_
    funext k
    simp [eMat, h _ h1]

theorem compare {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (hι : HSpace.IsIsomEmb A B ι) :
    (∀ d : BesselDatum A B ι, ∃ b : BesDat A B ι, (b.y : GA D B) = 1 ∧ (∀ i, b.c i = d.θ) ∧ Same b d) ∧
    (∀ (b : BesDat A B ι) (θ : D.host.E), θ ≠ 0 → ∃ d : BesselDatum A B ι, d.θ = θ ∧ Same b d) ∧
    ∀ (b : BesDat A B ι) (d : BesselDatum A B ι), Same b d → (b.y : GA D B) = 1 → ∀ ψ μ 𝓕 s φ F C a,
      ClauseFlag ψ b μ 𝓕 s φ F C a ↔ ClauseDual ψ d μ 𝓕 s φ F C a :=
  ⟨fun d => ⟨toBes d, rfl, fun _ => rfl, same_toBes d⟩, exists_same hι, fun _ _ h hy => clause_iff h hy⟩

end GlobalTheory.BesselCompare

end
