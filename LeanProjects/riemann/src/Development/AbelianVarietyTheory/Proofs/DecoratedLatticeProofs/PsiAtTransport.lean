import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk

noncomputable section

namespace GlobalTheory.Transport.Pen

section Val

open Matrix

variable {k Γ : Type} [Field k] [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ) {a b c : ℕ}

def Le (A : Matrix (Fin a) (Fin b) k) : Prop := ∀ i j, v (A i j) ≤ 1

def Lt (A : Matrix (Fin a) (Fin b) k) : Prop := ∀ i j, v (A i j) < 1

variable {v}

theorem Lt.le {A : Matrix (Fin a) (Fin b) k} (h : Lt v A) : Le v A := fun i j => (h i j).le

theorem Le.add {A B : Matrix (Fin a) (Fin b) k} (h : Le v A) (h' : Le v B) : Le v (A + B) :=
  fun i j => Valuation.map_add_le _ (h i j) (h' i j)

theorem Le.sub {A B : Matrix (Fin a) (Fin b) k} (h : Le v A) (h' : Le v B) : Le v (A - B) :=
  fun i j => Valuation.map_sub_le _ (h i j) (h' i j)

theorem Lt.add {A B : Matrix (Fin a) (Fin b) k} (h : Lt v A) (h' : Lt v B) : Lt v (A + B) :=
  fun i j => Valuation.map_add_lt _ (h i j) (h' i j)

theorem Lt.sub {A B : Matrix (Fin a) (Fin b) k} (h : Lt v A) (h' : Lt v B) : Lt v (A - B) :=
  fun i j => Valuation.map_sub_lt _ (h i j) (h' i j)

theorem Le.mul {A : Matrix (Fin a) (Fin b) k} {B : Matrix (Fin b) (Fin c) k} (h : Le v A) (h' : Le v B) : Le v (A * B) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_one' (h i l) (h' l j)

theorem Le.mul_lt {A : Matrix (Fin a) (Fin b) k} {B : Matrix (Fin b) (Fin c) k} (h : Le v A) (h' : Lt v B) : Lt v (A * B) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Valuation.map_sum_lt _ one_ne_zero fun l _ => by
      rw [map_mul]; exact (mul_le_of_le_one_left' (h i l)).trans_lt (h' l j)

theorem Lt.mul_le {A : Matrix (Fin a) (Fin b) k} {B : Matrix (Fin b) (Fin c) k} (h : Lt v A) (h' : Le v B) : Lt v (A * B) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Valuation.map_sum_lt _ one_ne_zero fun l _ => by
      rw [map_mul]; exact (mul_le_of_le_one_right' (h' l j)).trans_lt (h i l)

theorem Lt.le_of_sub_one {A : Matrix (Fin a) (Fin a) k} (h : Lt v (A - 1)) : Le v A := by
  have h1 : Le v (1 : Matrix (Fin a) (Fin a) k) := GlobalTheory.Mem.ColAd.sm_one (v := v)
  have := h.le.add h1
  rwa [sub_add_cancel] at this

theorem le_of_mul_left {A : Matrix (Fin a) (Fin a) k} {B : Matrix (Fin a) (Fin b) k} (h : Lt v (A - 1)) (h' : Le v (A * B)) :
    Le v B := by
  intro i j
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin a × Fin a)) (fun l => v ((A - 1) l.1 l.2))
    ⟨(i, i), Finset.mem_univ _⟩
  exact GlobalTheory.Mem.ColAd.int_of_mulVec (v := v) (A := A) (fun r s => hm (r, s) (Finset.mem_univ _)) (h _ _) (x := fun l => B l j)
    (fun r => h' r j) i

theorem le_of_mul_right {A : Matrix (Fin b) (Fin b) k} {B : Matrix (Fin a) (Fin b) k} (h : Lt v (A - 1)) (h' : Le v (B * A)) :
    Le v B := by
  have := le_of_mul_left (v := v) (A := Aᵀ) (B := Bᵀ) (fun i j => by
    have := h j i
    rwa [Matrix.sub_apply, Matrix.one_apply, show (if j = i then (1 : k) else 0) = (1 : Matrix (Fin b) (Fin b) k) i j by
      rw [Matrix.one_apply]; exact if_congr eq_comm rfl rfl] at this) (fun i j => by
    rw [← Matrix.transpose_mul]; exact h' j i)
  exact fun i j => this j i

theorem two_sided {A : Matrix (Fin a) (Fin a) k} {B : Matrix (Fin b) (Fin b) k} {X Z : Matrix (Fin a) (Fin b) k}
    (hA : Lt v (A - 1)) (hB : Lt v (B - 1)) (e : A * X = Z * B) : (Le v X ↔ Le v Z) ∧ (Le v X → Lt v (X - Z)) := by
  have h1 : Le v X → Le v Z := fun h => le_of_mul_right hB (e ▸ hA.le_of_sub_one.mul h)
  refine ⟨⟨h1, fun h => le_of_mul_left hA (e ▸ h.mul hB.le_of_sub_one)⟩, fun h => ?_⟩
  have e2 : X - Z = Z * (B - 1) - (A - 1) * X := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e2]
  exact ((h1 h).mul_lt hB).sub (hA.mul_le h)

end Val

section Frames

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep GlobalTheory.Mem.ColAd Matrix
open GlobalTheory.Mem.Col2.PtExist (mat mat_mulVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n a b : ℕ}
  {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem lift_cong {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (w : SG) {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsLiftFr p.deco.1 w f) : Lt Valued.v (locM w.1 g⁻¹ * ratM w.1 f - 1) := by
  classical
  intro i j
  obtain ⟨s, hs, h1⟩ := (mem_locP _ _ _).1 ((hf.1 _).2 (single_mem_stdAt j))
  obtain ⟨r, hr, h2⟩ := h.be w _ h1 i
  have h3 : p.deco.1.be w (s • f (Pi.single j 1)) i = Ideal.Quotient.mk w.1.asIdeal (s * if i = j then 1 else 0) := by
    rw [p.deco.2.be_smul w s _ ((hf.1 _).2 (single_mem_stdAt j)), hf.2 _ (single_mem_stdAt j), Pi.smul_apply, smul_eq_mul, map_mul]
    congr 1
    rw [← reduction_coe]
    unfold redV
    rw [Pi.single_apply]
    congr 1
    split_ifs <;> simp
  rw [h3, Ideal.Quotient.eq] at hr
  have h4 : Valued.v (algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E (r - s * if i = j then 1 else 0))) < 1 := by
    rw [valued_algebraMap, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hr
  have h5 : Valued.v (algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E s)) = 1 := by
    rw [valued_algebraMap]
    exact CharValCompare.val_of_notMem hs
  have e : adAt F w.1 (Col2.pullV g (s • f (Pi.single j 1)) i) =
      algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E s) * (locM w.1 g⁻¹ * ratM w.1 f) i j := by
    simp only [Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE, Matrix.mul_apply, Finset.mul_sum, Pi.smul_apply,
      Algebra.smul_def]
    exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm]; rfl
  have h6 := Valuation.map_add_lt _ h2 h4
  rw [e, map_sub, map_sub, sub_add_sub_cancel, map_mul, map_mul, ← mul_sub, map_mul, h5, one_mul] at h6
  rw [Matrix.sub_apply, Matrix.one_apply]
  convert h6 using 3
  split_ifs <;> simp

def homM (P : HeightOneSpectrum (𝓞 E)) (x : HomE E a b) : Matrix (Fin b) (Fin a) (P.adicCompletion E) :=
  (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E))

omit [StarRing E] in

theorem ratM_mul_homM (P : HeightOneSpectrum (𝓞 E)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    ratM P f' * homM P (inFr f f' x) = homM P x * ratM P f := by
  have e : ∀ {m : ℕ} (g : Sp E m ≃ₗ[E] Sp E m), ratM P g = homM P g.toLinearMap := fun g => by
    ext i j
    simp [ratM, homM, mat]
  rw [e, e]
  unfold homM
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 2
  exact LinearMap.ext fun z => f'.apply_symm_apply _

theorem mem_homS_iff (P : HeightOneSpectrum (𝓞 E)) (x : HomE E a b) :
    x ∈ GlobalTheory.LastSteps.homS (stdAt E a P) (stdAt E b P) ↔ Le Valued.v (homM P x) := by
  have e : ∀ i j, homM P x i j = algebraMap E _ (x (Pi.single j 1) i) := fun i j => by simp [homM]
  refine ⟨fun h i j => ?_, fun h y hy => mem_stdAt.2 fun i => ?_⟩
  · rw [e]
    exact mem_stdAt_val.1 (h _ (single_mem_stdAt j)) i
  · rw [apply_eq_sum]
    refine intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul ?_
    have := h i j
    rwa [e, valued_algebraMap, ← CharValCompare.intAt_iff] at this

omit [StarRing E] in

theorem val_le_q {P : HeightOneSpectrum (𝓞 E)} (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {z : WithZero (Multiplicative ℤ)}
    (hz : z < 1) : z ≤ P.valuation E ((qOf P : ℕ) : E) := by
  have e : P.valuation E ((qOf P : ℕ) : E) = P.intValuation ((qOf P : ℕ) : 𝓞 E) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    simp
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, not_le] at hq
  rw [e]
  generalize P.intValuation ((qOf P : ℕ) : 𝓞 E) = t at hq
  by_cases h0 : z = 0
  · simp [h0]
  have ht : t ≠ 0 := (zero_le.trans_lt hq).ne'
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
  rw [← WithZero.exp_log ht, WithZero.exp_lt_exp] at hq
  rw [← WithZero.exp_log h0, ← WithZero.exp_log ht, WithZero.exp_le_exp]
  push_cast at hq
  omega

theorem good_eq {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {Φ : HomE E a b → K}
    (hΦ : GlobalTheory.LastSteps.Good P (GlobalTheory.LastSteps.homS (stdAt E a P) (stdAt E b P)) Φ) {x x₀ : HomE E a b}
    (h1 : Le Valued.v (homM P x) ↔ Le Valued.v (homM P x₀)) (h2 : Le Valued.v (homM P x) → Lt Valued.v (homM P x - homM P x₀)) :
    Φ x₀ = Φ x := by
  by_cases h : Le Valued.v (homM P x)
  · have hq0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
    have hz : ((qOf P : ℕ) : E)⁻¹ • (x - x₀) ∈ GlobalTheory.LastSteps.homS (stdAt E a P) (stdAt E b P) := by
      refine (mem_homS_iff P _).2 fun i j => ?_
      have h3 := val_le_q hq (h2 h i j)
      have e : homM P (((qOf P : ℕ) : E)⁻¹ • (x - x₀)) i j =
          algebraMap E _ ((qOf P : ℕ) : E)⁻¹ * (homM P x - homM P x₀) i j := by
        simp [homM]
      rw [e, map_mul, valued_algebraMap, map_inv₀]
      exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hq0))).2 h3
    have := hΦ.2.1 x₀ _ hz
    rw [smul_inv_smul₀ hq0, add_sub_cancel] at this
    exact this.symm
  · have a1 : Φ x = 0 := by_contra fun h0 => h ((mem_homS_iff P _).1 (hΦ.1 _ h0))
    have a2 : Φ x₀ = 0 := by_contra fun h0 => h (h1.2 ((mem_homS_iff P _).1 (hΦ.1 _ h0)))
    rw [a1, a2]

theorem le_ratM {P : HeightOneSpectrum (𝓞 E)} {f : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ x, f x ∈ stdAt E n P ↔ x ∈ stdAt E n P) :
    Le Valued.v (ratM P f) ∧ Le Valued.v (ratM P f⁻¹) :=
  ⟨sm_glint (⟨f, hf⟩ : GLint E n P), sm_glint ((⟨f, hf⟩ : GLint E n P)⁻¹)⟩

theorem frames_cong {P : HeightOneSpectrum (𝓞 E)} {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)}
    {f g : Sp E a ≃ₗ[E] Sp E a} {f' g' : Sp E b ≃ₗ[E] Sp E b}
    (hf : ∀ x, f x ∈ stdAt E a P ↔ x ∈ stdAt E a P) (hf' : ∀ x, f' x ∈ stdAt E b P ↔ x ∈ stdAt E b P)
    (c1 : Lt Valued.v (locM P k⁻¹ * ratM P f - 1)) (c2 : Lt Valued.v (locM P k'⁻¹ * ratM P f' - 1))
    (c3 : Lt Valued.v (locM P (y * k)⁻¹ * ratM P g - 1)) (c4 : Lt Valued.v (locM P (y' * k')⁻¹ * ratM P g' - 1))
    {x x₀ : HomE E a b} (hx : Lt Valued.v (locM P y'⁻¹ * homM P x * locM P y - homM P x₀)) :
    (Le Valued.v (homM P (inFr g g' x)) ↔ Le Valued.v (homM P (inFr f f' x₀))) ∧
      (Le Valued.v (homM P (inFr g g' x)) → Lt Valued.v (homM P (inFr g g' x) - homM P (inFr f f' x₀))) := by
  have hk : Le Valued.v (locM P k) := le_of_mul_right c1 (by
    rw [← Matrix.mul_assoc, ← locM_mul, mul_inv_cancel, locM_one, Matrix.one_mul]
    exact (le_ratM hf).1)
  have hk' : Le Valued.v (locM P k'⁻¹) := by
    have := c2.le_of_sub_one.mul (le_ratM hf').2
    rwa [Matrix.mul_assoc, ← ratM_mul, mul_inv_cancel, ratM_one, Matrix.mul_one] at this
  have hD := (hk'.mul_lt hx).mul_le hk
  have e1 := two_sided c2 c1 (X := homM P (inFr f f' x₀)) (Z := locM P k'⁻¹ * homM P x₀ * locM P k) (by
    rw [Matrix.mul_assoc, ratM_mul_homM, Matrix.mul_assoc, ← Matrix.mul_assoc (locM P k), ← locM_mul, mul_inv_cancel, locM_one,
      Matrix.one_mul, Matrix.mul_assoc])
  have e2 := two_sided c4 c3 (X := homM P (inFr g g' x)) (Z := locM P (y' * k')⁻¹ * homM P x * locM P (y * k)) (by
    rw [Matrix.mul_assoc, ratM_mul_homM, Matrix.mul_assoc, ← Matrix.mul_assoc (locM P (y * k)), ← locM_mul, mul_inv_cancel, locM_one,
      Matrix.one_mul, Matrix.mul_assoc])
  have e3 : locM P k'⁻¹ * (locM P y'⁻¹ * homM P x * locM P y - homM P x₀) * locM P k =
      locM P (y' * k')⁻¹ * homM P x * locM P (y * k) - locM P k'⁻¹ * homM P x₀ * locM P k := by
    rw [_root_.mul_inv_rev, locM_mul, locM_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  rw [e3] at hD
  have e4 : Le Valued.v (locM P (y' * k')⁻¹ * homM P x * locM P (y * k)) ↔ Le Valued.v (locM P k'⁻¹ * homM P x₀ * locM P k) :=
    ⟨fun h => by simpa only [sub_sub_cancel] using h.sub hD.le, fun h => by simpa only [sub_add_cancel] using hD.le.add h⟩
  have e5 := e2.1.trans (e4.trans e1.1.symm)
  refine ⟨e5, fun h => ?_⟩
  have := ((e2.2 h).add hD).sub (e1.2 (e5.1 h))
  rwa [sub_add_sub_cancel, sub_sub_sub_cancel_right] at this

end Frames

end GlobalTheory.Transport.Pen

namespace GlobalTheory.Transport.Pen

section Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem psiAt_cosetIn (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) {u : Pr.Word}
    (p q : PtAt R sel mu cst u (m2 + 1)) (h : cosetIn q = cosetIn p) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) :
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x ((frsF sel mu p.1.1 P).symm (repY p.1.2)) =
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) x ((frsF sel mu q.1.1 P).symm (repY q.1.2)) := by
  have hm : m2 + 1 + 1 = R.m := hL.hm.symm
  have h1 : (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ cosetIn p P := ⟨_, p.repY_mem hm, by simp⟩
  rw [← h] at h1
  obtain ⟨z, hz, h2⟩ := h1
  rw [if_pos hP, pow_zero, inv_one, one_smul] at h2
  have h3 := add_mem h2 ((GlobalTheory.TopLaw.coset_sub q.1.1 (q.mem_ybSet hm) hz (q.repY_mem hm) P).1 hP)
  rw [sub_add_sub_cancel] at h3
  have h4 := hL.psiInv al P x ((frsF sel mu q.1.1 P).symm (repY q.1.2)) _ fun i => by
    rw [if_pos hP, pow_zero, inv_one, one_mul]
    exact mem_stdAt.1 h3 i
  rwa [add_sub_cancel] at h4

theorem psiAt_frames (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    {u : Pr.Word} {F : Type} [Field F] [NumberField F] [Algebra F X.E] {hc : CMData F X.E}
    (p q : PtAt R sel mu cst u m2) (p' q' : PtAt R sel mu cst u (m2 + 1)) {k y : GL (Fin (R.N m2)) (AfE F X.E)}
    {k' y' : GL (Fin (R.N (m2 + 1))) (AfE F X.E)} (hp : IsPtOf hc k p.1.1) (hN : p.1.1.deco.1.N = stdLat X.E _)
    (hp' : IsPtOf hc k' p'.1.1) (hN' : p'.1.1.deco.1.N = stdLat X.E _) (hq : IsPtOf hc (y * k) q.1.1)
    (hq' : IsPtOf hc (y' * k') q'.1.1) (h : cosetIn q' = cosetIn p') {x x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))}
    (hx : Lt Valued.v (ColAd.locM P.1 y'⁻¹ * homM P.1 x * ColAd.locM P.1 y - homM P.1 x₀)) :
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p.1.1 P) (frsF sel mu p'.1.1 P) x₀)
        ((frsF sel mu p'.1.1 P).symm (repY p'.1.2)) =
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu q.1.1 P) (frsF sel mu q'.1.1 P) x)
        ((frsF sel mu q'.1.1 P).symm (repY q'.1.2)) := by
  rw [psiAt_cosetIn hL al P hP p' q' h]
  have hlift : ∀ {j : ℕ} (r : ChPt (R := R) sel mu u j), IsLiftFr r.deco.1 ⟨P.1, hP⟩ (frsF sel mu r P) := fun r => by
    unfold frsF
    rw [dif_pos hP]
    exact liftFr_spec r.deco.2 _
  have key := frames_cong (P := P.1) (k := k) (y := y) (k' := k') (y' := y')
    (f := frsF sel mu p.1.1 P) (g := frsF sel mu q.1.1 P) (f' := frsF sel mu p'.1.1 P) (g' := frsF sel mu q'.1.1 P)
    (fun z => by have := (hlift p.1.1).1 z; rwa [Deco.at, hN] at this)
    (fun z => by have := (hlift p'.1.1).1 z; rwa [Deco.at, hN'] at this)
    (lift_cong hp ⟨P.1, hP⟩ (hlift p.1.1)) (lift_cong hp' ⟨P.1, hP⟩ (hlift p'.1.1)) (lift_cong hq ⟨P.1, hP⟩ (hlift q.1.1))
    (lift_cong hq' ⟨P.1, hP⟩ (hlift q'.1.1)) hx
  have h1 := good_eq (qOf_notMem_sq hX hPr hP) (GlobalTheory.LastSteps.good_PsiAt Ch sel mu cst hL.hm P hP (hL.stabG m2 al P hP)
    ((frsF sel mu q'.1.1 P).symm (repY q'.1.2))) key.1 key.2
  exact h1

end Local

section Cong

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep

theorem lt_of_congAt {B : Base} {a b : ℕ} {P : HeightOneSpectrum (𝓞 B.host.E)} {c : ℕ} {y : TC.GA B a} {y' : TC.GA B b}
    {x x₀ : HomE B.host.E a b} (hx : GlobalTheory.Transport.CongAt B P (qOf P * c) y y' x x₀) :
    Lt Valued.v (ColAd.locM P y'⁻¹ * homM P x * ColAd.locM P y - homM P x₀) := by
  have hv : Valued.v (((qOf P * c : ℕ) : ℕ) : P.adicCompletion B.host.E) < 1 := by
    rw [← map_natCast (algebraMap B.host.E (P.adicCompletion B.host.E)), valued_algebraMap, Nat.cast_mul, map_mul]
    refine (mul_le_of_le_one_right' ?_).trans_lt ColAd.val_qOf_lt
    exact GlobalTheory.CharValCompare.intAt_iff.1 (intAt_nat _)
  intro r s
  refine lt_of_le_of_lt (le_of_eq_of_le ?_ (hx r s)) hv
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, adAt_inclE, ColAd.locM, homM]

end Cong

end GlobalTheory.Transport.Pen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
