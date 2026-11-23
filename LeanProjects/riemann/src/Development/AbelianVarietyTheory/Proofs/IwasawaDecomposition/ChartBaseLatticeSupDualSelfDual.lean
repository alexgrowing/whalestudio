import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.ChartBase

open NumberField

variable {E : Type} [Field E] [NumberField E]

theorem hform_one (σ : E →+* E) {n : ℕ} (x y : Fin n → E) :
    Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold Formalism.UG.hform
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.one_apply]

theorem sig_int (σ : E →+* E) (s : 𝓞 E) : σ (s : E) ∈ (algebraMap (𝓞 E) E).range :=
  ⟨RingOfIntegers.mapRingHom σ s, rfl⟩

theorem sup_dual_eq (σ : E →+* E) {n : ℕ} (t pb : 𝓞 E) (ht : (t : E) ≠ 0) (hpb : (pb : E) = σ t)
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = r ∧ (j.1 + 1 = n → t ∣ r))
    (M : Submodule (𝓞 E) (Fin n → E))
    (hM : ∀ x, x ∈ M ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range) :
    Λ ⊔ Ideal.span {pb} • Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) Λ) = M := by
  classical
  have hσt : σ (t : E) ≠ 0 := (map_ne_zero σ).2 ht
  have hpb0 : (pb : E) ≠ 0 := by rw [hpb]; exact hσt
  apply le_antisymm
  · refine sup_le (fun x hx => (hM x).2 fun j => ?_) ?_
    · obtain ⟨r, hr, -⟩ := (hΛ x).1 hx j
      exact ⟨r, hr.symm⟩
    ·
      have key : ∀ y ∈ Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) Λ), pb • y ∈ M := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          refine (hM _).2 fun j => ?_
          have hs : ∀ c : 𝓞 E, (∀ j' : Fin n, j'.1 + 1 = n → t ∣ (if j' = j then c else 0)) →
              Pi.single j (c : E) ∈ Λ := by
            intro c hc
            refine (hΛ _).2 fun j' => ⟨if j' = j then c else 0, ?_, hc j'⟩
            by_cases h : j' = j
            · subst h; simp
            · simp [h, Pi.single_apply]
          have hval : ∀ c : 𝓞 E, Pi.single j (c : E) ∈ Λ → σ (c : E) * y j ∈ (algebraMap (𝓞 E) E).range := by
            intro c hc
            have := hy _ hc
            rw [hform_one] at this
            rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)] at this
            simpa using this
          show ((pb • y) j) ∈ _
          rw [Pi.smul_apply, Algebra.smul_def]
          by_cases hj : j.1 + 1 = n
          · have h1 := hval t (hs t fun j' _ => by split_ifs <;> simp)
            rw [show algebraMap (𝓞 E) E pb = (pb : E) from rfl, hpb]
            exact h1
          · have h1 := hval 1 (hs 1 fun j' hj' => by
              split_ifs with h
              · subst h; exact absurd hj' hj
              · simp)
            have h1' : y j ∈ (algebraMap (𝓞 E) E).range := by simpa using h1
            obtain ⟨a, ha⟩ := h1'
            exact ⟨pb * a, by rw [map_mul, ha]⟩
        | zero => simpa using M.zero_mem
        | add a b _ _ ha hb => rw [smul_add]; exact M.add_mem ha hb
        | smul c a _ ha => rw [smul_comm]; exact M.smul_mem c ha
      refine Submodule.smul_le.2 fun r hr y hy => ?_
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [mul_smul]
      exact M.smul_mem a (key y hy)
  · intro x hx
    have hx' := (hM x).1 hx
    let x1 : Fin n → E := fun j => if j.1 + 1 = n then 0 else x j
    let z : Fin n → E := fun j => if j.1 + 1 = n then x j / (pb : E) else 0
    have hsplit : x = x1 + pb • z := by
      funext j
      simp only [x1, z, Pi.add_apply, Pi.smul_apply, Algebra.smul_def]
      split_ifs
      · rw [show algebraMap (𝓞 E) E pb = (pb : E) from rfl]; field_simp; ring
      · simp
    rw [hsplit]
    refine Submodule.add_mem_sup ?_ ?_
    · refine (hΛ _).2 fun j => ?_
      by_cases hj : j.1 + 1 = n
      · exact ⟨0, by simp [x1, hj], fun _ => dvd_zero _⟩
      · obtain ⟨r, hr⟩ := hx' j
        exact ⟨r, by simp [x1, hj, hr], fun h => absurd h hj⟩
    · refine Submodule.smul_mem_smul (Ideal.mem_span_singleton_self pb) (Submodule.subset_span ?_)
      intro x0 hx0
      rw [hform_one]
      refine Subring.sum_mem _ fun i _ => ?_
      by_cases hi : i.1 + 1 = n
      · obtain ⟨r, hr, hd⟩ := (hΛ x0).1 hx0 i
        obtain ⟨s, rfl⟩ := hd hi
        obtain ⟨a, ha⟩ := hx' i
        simp only [z, hi, if_true, hr]
        have e : σ ((t * s : 𝓞 E) : E) * (x i / (pb : E)) = σ (s : E) * x i := by
          rw [hpb]; push_cast; rw [map_mul]; field_simp
        rw [e, ← ha]
        obtain ⟨b, hb⟩ := sig_int σ s
        exact ⟨b * a, by rw [map_mul, hb]⟩
      · simp only [z, hi, if_false, mul_zero]
        exact Subring.zero_mem _

end GlobalTheory.Mem.Col2.TC.ChartBase

namespace GlobalTheory.Mem.Col2.TC.ChartBase

open NumberField

variable {E : Type} [Field E] [NumberField E]

theorem mem_reL_iff {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin a → E)) (x : Fin a → E) :
    x ∈ L ↔ Formalism.L2.Forms.reV h E x ∈ Formalism.L2.Forms.reL h L := by
  subst h
  have e : ∀ y : Fin a → E, Formalism.L2.Forms.reV rfl E y = y := fun y => by
    funext j; simp [Formalism.L2.Forms.reV]
  constructor
  · intro hx; exact Submodule.mem_map.2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    have : y = x := by
      have := hyx
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, e] at this
      exact this
    exact this ▸ hy

theorem reV_apply {a b : ℕ} (h : a = b) (x : Fin a → E) (j : Fin b) :
    Formalism.L2.Forms.reV h E x j = x (Fin.cast h.symm j) := by
  subst h; simp [Formalism.L2.Forms.reV]

end GlobalTheory.Mem.Col2.TC.ChartBase

namespace GlobalTheory.Mem.Col2.TC.ChartBase

theorem mem_of_baseL {B : Base} {a b : ℕ} (h : a = b) (t : 𝓞 B.host.E) (L : Submodule (𝓞 B.host.E) (Fin a → B.host.E))
    (L' : Submodule (𝓞 B.host.E) (Fin b → B.host.E)) (hL' : L' = Formalism.L2.Forms.reL h L)
    (hb : ∀ x, x ∈ L' ↔ x ∈ baseL B b t) (x : Fin a → B.host.E) :
    x ∈ L ↔ ∀ j : Fin a, ∃ r : 𝓞 B.host.E, x j = r ∧ (j.1 + 1 = a → t ∣ r) := by
  rw [mem_reL_iff h L x, ← hL', hb]
  unfold baseL
  simp only [Set.mem_setOf_eq, reV_apply]
  constructor
  · intro H j
    obtain ⟨r, hr, hd⟩ := H (Fin.cast h j)
    exact ⟨r, by simpa using hr, fun hj => hd (by simp [← h, hj])⟩
  · intro H j
    obtain ⟨r, hr, hd⟩ := H (Fin.cast h.symm j)
    exact ⟨r, hr, fun hj => hd (by simp [h, hj])⟩

end GlobalTheory.Mem.Col2.TC.ChartBase

open GlobalTheory.Mem.Col2.TC.ChartBase in

theorem GlobalTheory.Mem.Col2.TC.chart_base_sup_dual : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), (H.lev u i h1 hm β).Lb ⊔ Ideal.span {pb} • Formalism.L2.Herm.dualL (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 hm β).Lb = Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0 := by
  intro B X I hOk hP l Z H F A hS hH hT u pb hpb i h1 hm β
  have hC := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hP l Z
  obtain ⟨hG, hL0, -⟩ := hC.2.2.2 i hm

  have hG1 : ((I.rec7 l Z).sp.X i).gram = 1 := by
    ext a b
    have := congrFun (congrFun hG (finCongr (rankN (I.rec7 l Z) i hm) a)) (finCongr (rankN (I.rec7 l Z) i hm) b)
    simpa [gramN, Matrix.one_apply] using this

  have hσ : ∀ x : (I.rec7 l Z).host.E, ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) x = (I.rec7 l Z).host.conj x := fun x => by
    have := (I.rec7 l Z).host.isCMField_hostE
    exact (I.rec7 l Z).host.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ (I.rec7 l Z).host.φ₀ x).trans
      ((I.rec7 l Z).host.conjE_apply (I.rec7 l Z).host.φ₀ x).symm)

  have hpi : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  have hT0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := fun h0 => by
    have e := X.piT_norm u
    rw [h0, zero_mul] at e
    exact (B.T_prime u).ne_zero (by exact_mod_cast e.symm)

  have hM : ∀ x, x ∈ Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0 ↔ ∀ j, x j ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range := by
    intro x
    rw [mem_reL_iff (rankN (I.rec7 l Z) i hm) _ x]
    have e : Formalism.L2.Forms.reL (rankN (I.rec7 l Z) i hm)
        (Formalism.L2.Herm.crdLat ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X i).L0) = selfDualLatticeCoords (I.rec7 l Z) i hm := by
      unfold Formalism.L2.Forms.reL Formalism.L2.Herm.crdLat
      rw [← Submodule.map_comp]; rfl
    rw [e, hL0]
    simp only [reV_apply]
    constructor
    · intro H j
      have h' := H (Fin.cast (rankN (I.rec7 l Z) i hm) j)
      rwa [Fin.cast_cast, Fin.cast_eq_self] at h'
    · intro H j; exact H _

  have hΛ : ∀ x, x ∈ (H.lev u i h1 hm β).Lb ↔ ∀ j : Fin ((I.rec7 l Z).sp.X i).rank, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = r ∧
      (j.1 + 1 = ((I.rec7 l Z).sp.X i).rank → X.piT u ∣ r) := by
    rcases Nat.lt_or_ge i (I.rec7 l Z).R.m with hlt | hge
    · have h2 : i + 1 ≤ (I.rec7 l Z).R.m := hlt
      have hc := hH.carC u i h1 h2 β
      obtain ⟨k, hk⟩ := (hS u).1.mid i h1 h2
      exact mem_of_baseL (rankN (I.rec7 l Z) i (le_of_succ_m h2)) (X.piT u) _ _ hc.Lb_eq (hk.lb β)
    · obtain rfl : i = (I.rec7 l Z).R.m := le_antisymm hm hge
      obtain rfl : β = chM H u := @Unique.eq_default _ (H.Ch_m u).some β
      have hc := hH.carM u
      obtain ⟨k, hk⟩ := (hS u).1.ends _ le_rfl (Or.inr rfl)
      exact mem_of_baseL (rankN (I.rec7 l Z) _ le_rfl) (X.piT u) _ _ hc.Lb_eq (hk.lb ())
  unfold Formalism.L2.Herm.dualL
  rw [hG1]
  exact sup_dual_eq _ (X.piT u) pb hT0 (by
    have e := hσ ((X.piT u : 𝓞 B.host.E) : B.host.E)
    rw [hpi] at hpb
    exact hpb.trans e.symm) _ hΛ _ hM
