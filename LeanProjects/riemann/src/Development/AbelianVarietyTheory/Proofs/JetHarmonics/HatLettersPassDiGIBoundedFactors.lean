import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD

namespace GlobalTheory.HatNF.Den

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.P.RuleGD

section level

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

def fm : Submonoid A := Submonoid.closure L.fns

lemma of_fns {x : A} (h : x ∈ L.fns) : x ∈ fm L := Submonoid.subset_closure h

lemma prod_mem {n : ℕ} (f : Fin n → A) (h : ∀ i, f i ∈ L.fns) : (List.ofFn f).prod ∈ fm L := by
  apply Submonoid.list_prod_mem
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact of_fns L (h i)

lemma comm_fm {x : A} (hx : ∀ f ∈ L.fns, Commute x f) {y : A} (hy : y ∈ fm L) : Commute x y := by
  have hy' : y ∈ Submonoid.closure L.fns := hy
  clear hy
  induction hy' using Submonoid.closure_induction with
  | mem f hf => exact hx f hf
  | one => exact Commute.one_right x
  | mul a b _ _ ha hb => exact ha.mul_right hb

lemma fm_comm {x y : A} (hx : x ∈ fm L) (hy : y ∈ fm L) : Commute x y := by
  refine comm_fm L (fun f hf => ?_) hy
  have hx' : x ∈ Submonoid.closure L.fns := hx
  clear hx hy
  induction hx' using Submonoid.closure_induction with
  | mem z hz => exact Formalism.FourierDecayAlt.P.RuleGD.fc L hz hf
  | one => exact Commute.one_left f
  | mul a b _ _ ha hb => exact ha.mul_left hb

lemma mDr : L.Dr ∈ fm L := Den.prod_mem L L.c (m_c L)
lemma mDrb : L.Drb ∈ fm L := Den.prod_mem L L.cb (m_cb L)
lemma mDri : L.Dri ∈ fm L := Den.prod_mem L L.ci (m_ci L)
lemma mDrbi : L.Drbi ∈ fm L := Den.prod_mem L L.cbi (m_cbi L)
lemma mD : L.D ∈ fm L := by
  show L.Dr * L.ζ ∈ fm L
  exact mul_mem (mDr L) (of_fns L (m_ζ L))
lemma mDb : L.Db ∈ fm L := by
  show L.Drb * L.ζb ∈ fm L
  exact mul_mem (mDrb L) (of_fns L (m_ζb L))
lemma mDi : L.Di ∈ fm L := by
  show L.ζi * L.Dri ∈ fm L
  exact mul_mem (of_fns L (m_ζi L)) (mDri L)
lemma mDbi : L.Dbi ∈ fm L := by
  show L.ζbi * L.Drbi ∈ fm L
  exact mul_mem (of_fns L (m_ζbi L)) (mDrbi L)
lemma mG : L.G ∈ fm L := by
  show L.Dr * L.Drb * L.GG ∈ fm L
  exact mul_mem (mul_mem (mDr L) (mDrb L)) (of_fns L (m_GG L))

lemma D_Di : L.D * L.Di = 1 := by
  show L.Dr * L.ζ * (L.ζi * L.Dri) = 1
  rw [mul_assoc, ← mul_assoc L.ζ, L.ζ_ζi, one_mul, Formalism.FourierDecayAlt.P.RuleGD.Dr_Dri]

lemma Db_Dbi : L.Db * L.Dbi = 1 := by
  show L.Drb * L.ζb * (L.ζbi * L.Drbi) = 1
  rw [mul_assoc, ← mul_assoc L.ζb, L.ζb_ζbi, one_mul, Formalism.FourierDecayAlt.P.RuleGD.Drb_Drbi]

lemma drb_Di : L.Drb * L.Di = L.Db * L.Di * L.ζbi := by
  have h : Commute L.ζb L.Di := fm_comm L (of_fns L (m_ζb L)) (mDi L)
  show L.Drb * L.Di = L.Drb * L.ζb * L.Di * L.ζbi
  rw [mul_assoc L.Drb L.ζb L.Di, h.eq, mul_assoc L.Drb (L.Di * L.ζb) L.ζbi, mul_assoc L.Di L.ζb L.ζbi,
    L.ζb_ζbi, mul_one]

lemma Ahat_Di (Y : ℂ) : L.Ahat Y * L.Di = L.Di * L.Ahat (Y - 1) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L (Y - 1)).1
  rw [sub_add_cancel] at h
  rw [← h, mul_assoc (L.Di * L.Ahat (Y - 1)) L.D L.Di, D_Di, mul_one]

lemma raising_mul_D_inv (Y : ℂ) : L.R0 Y * L.Di =
    L.Di * L.R0 (Y - 1) - L.TT • (L.Db * L.Di * L.ζbi * L.Di * L.Ahat (Y - 1)) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L (Y - 1)).2.1
  rw [sub_add_cancel] at h
  have h2 : L.R0 Y = L.Di * L.R0 (Y - 1) * L.D - algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat Y) :=
    eq_sub_of_add_eq h.symm
  have e2 : L.Drb * L.Di * L.Ahat Y * L.Di = L.Db * L.Di * L.ζbi * L.Di * L.Ahat (Y - 1) := by
    rw [mul_assoc (L.Drb * L.Di) (L.Ahat Y) L.Di, Ahat_Di, drb_Di, ← mul_assoc (L.Db * L.Di * L.ζbi) L.Di]
  rw [h2, sub_mul, mul_assoc (L.Di * L.R0 (Y - 1)) L.D L.Di, D_Di, mul_one,
    mul_assoc (algebraMap ℂ A L.TT) (L.Drb * L.Di * L.Ahat Y) L.Di, e2, ← Algebra.smul_def]

lemma v_Di (Y : ℂ) : Commute L.Di (L.Ahatv Y) ∧ Commute L.Di (L.R0v Y) := by
  have h := (Formalism.FourierDecayAlt.P.shiftConjugation A r L Y).2.2.2.2.2
  have hci : ∀ l, L.ci l * L.Ahatv Y = L.Ahatv Y * L.ci l ∧ L.ci l * L.R0v Y = L.R0v Y * L.ci l :=
    fun l => h _ (by simp)
  have hzi := h L.ζi (by simp)
  have a1 : Commute L.Dri (L.Ahatv Y) :=
    (Formalism.FourierDecayAlt.P.RuleGD.comm_prod L.ci (L.Ahatv Y) fun i => ((hci i).1).symm).symm
  have a2 : Commute L.Dri (L.R0v Y) :=
    (Formalism.FourierDecayAlt.P.RuleGD.comm_prod L.ci (L.R0v Y) fun i => ((hci i).2).symm).symm
  exact ⟨(show Commute L.ζi (L.Ahatv Y) from hzi.1).mul_left a1,
    (show Commute L.ζi (L.R0v Y) from hzi.2).mul_left a2⟩

end level

section star

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

lemma mgI : TL.gI L ∈ fm L := by
  show L.Dri * L.Drbi * L.GGi ∈ fm L
  exact mul_mem (mul_mem (mDri L) (mDrbi L)) (of_fns L (m_GGi L))

lemma G_gI : L.G * TL.gI L = 1 := by
  show L.Dr * L.Drb * L.GG * (L.Dri * L.Drbi * L.GGi) = 1
  have c1 : Commute L.GG L.Dri := fm_comm L (of_fns L (m_GG L)) (mDri L)
  have c2 : Commute L.Drb L.Dri := fm_comm L (mDrb L) (mDri L)
  have c3 : Commute L.GG L.Drbi := fm_comm L (of_fns L (m_GG L)) (mDrbi L)
  simp only [mul_assoc]
  rw [c1.left_comm, c2.left_comm, c3.left_comm, L.GG_GGi, mul_one, Formalism.FourierDecayAlt.P.RuleGD.Drb_Drbi, mul_one, Formalism.FourierDecayAlt.P.RuleGD.Dr_Dri]

lemma gI_G : TL.gI L * L.G = 1 := by
  show L.Dri * L.Drbi * L.GGi * (L.Dr * L.Drb * L.GG) = 1
  have c1 : Commute L.GGi L.Dr := fm_comm L (of_fns L (m_GGi L)) (mDr L)
  have c2 : Commute L.Drbi L.Dr := fm_comm L (mDrbi L) (mDr L)
  have c3 : Commute L.GGi L.Drb := fm_comm L (of_fns L (m_GGi L)) (mDrb L)
  simp only [mul_assoc]
  rw [c1.left_comm, c2.left_comm, c3.left_comm, L.GGi_GG, mul_one, Formalism.FourierDecayAlt.P.RuleGD.Drbi_Drb, mul_one, Formalism.FourierDecayAlt.P.RuleGD.Dri_Dr]

omit [StarRing A] in
lemma fn_G {z : A} (hz : z ∈ L.fns) : z * L.GGi * L.G = L.Dr * L.Drb * z := by
  show z * L.GGi * (L.Dr * L.Drb * L.GG) = L.Dr * L.Drb * z
  have c1 : Commute L.GGi L.Dr := fm_comm L (of_fns L (m_GGi L)) (mDr L)
  have c2 : Commute L.GGi L.Drb := fm_comm L (of_fns L (m_GGi L)) (mDrb L)
  have c3 : Commute z (L.Dr * L.Drb) := fm_comm L (of_fns L hz) (mul_mem (mDr L) (mDrb L))
  simp only [mul_assoc]
  rw [c1.left_comm, c2.left_comm, L.GGi_GG, mul_one, ← mul_assoc L.Dr L.Drb z, ← c3.eq]

lemma hats_gI (Y : ℂ) : L.Ahat Y * TL.gI L = TL.gI L * L.Ahat (Y - 1) ∧
    L.R0 Y * TL.gI L = TL.gI L * L.R0 (Y - 1) ∧ L.Ahatv Y * TL.gI L = TL.gI L * L.Ahatv (Y + 1) ∧
    L.R0v Y * TL.gI L = TL.gI L * L.R0v (Y + 1) := by
  have hfn : ∀ x ∈ L.fns, x * L.G = L.G * x := fun x hx => (fm_comm L (of_fns L hx) (mG L)).eq
  have hp : ∀ l, L.p l * L.G = L.G * L.p l + algebraMap ℂ A 1 * L.G := by
    intro l
    have hb : Commute (L.p l) L.Drb := Formalism.FourierDecayAlt.P.RuleGD.comm_prod L.cb (L.p l) (fun i => L.p_cb l i)
    have hg : Commute (L.p l) L.GG := L.p_GG l
    have e1 : SemiconjBy L.Dr (L.p l + 1) (L.p l) := by
      show L.Dr * (L.p l + 1) = L.p l * L.Dr
      rw [mul_add, mul_one, Formalism.FourierDecayAlt.P.RuleGD.p_Dr, one_mul]
    have e : SemiconjBy (L.Dr * L.Drb * L.GG) (L.p l + 1) (L.p l) :=
      (e1.mul_left (hb.symm.add_right (Commute.one_right _))).mul_left
        (hg.symm.add_right (Commute.one_right _))
    rw [map_one, one_mul]
    show L.p l * (L.Dr * L.Drb * L.GG) = L.Dr * L.Drb * L.GG * L.p l + L.Dr * L.Drb * L.GG
    rw [← e.eq, mul_add, mul_one]
  have hpb : ∀ l, L.pb l * L.G = L.G * L.pb l + algebraMap ℂ A 1 * L.G := by
    intro l
    have ha : Commute (L.pb l) L.Dr := Formalism.FourierDecayAlt.P.RuleGD.comm_prod L.c (L.pb l) (fun i => L.pb_c l i)
    have hg : Commute (L.pb l) L.GG := L.pb_GG l
    have e1 : SemiconjBy L.Drb (L.pb l + 1) (L.pb l) := by
      show L.Drb * (L.pb l + 1) = L.pb l * L.Drb
      rw [mul_add, mul_one, Formalism.FourierDecayAlt.P.RuleGD.pb_Drb, one_mul]
    have e : SemiconjBy (L.Dr * L.Drb * L.GG) (L.pb l + 1) (L.pb l) :=
      (SemiconjBy.mul_left ha.symm e1).mul_left (hg.symm.add_right (Commute.one_right _))
    rw [map_one, one_mul]
    show L.pb l * (L.Dr * L.Drb * L.GG) = L.Dr * L.Drb * L.GG * L.pb l + L.Dr * L.Drb * L.GG
    rw [← e.eq, mul_add, mul_one]
  have hnab : L.nab * L.G = L.G * L.nab + algebraMap ℂ A 1 * (L.ζb * L.GGi * L.G) := by
    have h1 : Commute L.nab L.Dr := Formalism.FourierDecayAlt.P.RuleGD.comm_prod L.c L.nab (fun i => L.nab_c i)
    have h2 : Commute L.nab L.Drb := Formalism.FourierDecayAlt.P.RuleGD.comm_prod L.cb L.nab (fun i => L.nab_cb i)
    rw [map_one, one_mul, fn_G L (m_ζb L)]
    show L.nab * (L.Dr * L.Drb * L.GG) = L.Dr * L.Drb * L.GG * L.nab + L.Dr * L.Drb * L.ζb
    simp only [← mul_assoc]
    rw [h1.eq, mul_assoc L.Dr L.nab L.Drb, h2.eq, ← mul_assoc L.Dr L.Drb L.nab,
      mul_assoc (L.Dr * L.Drb) L.nab L.GG, L.nab_GG, mul_add, ← mul_assoc (L.Dr * L.Drb) L.GG L.nab]
  have hnabs : L.nabs * L.G = L.G * L.nabs - algebraMap ℂ A 1 * (L.ζ * L.GGi * L.G) := by
    have h1 : Commute L.nabs L.Dr := Formalism.FourierDecayAlt.P.RuleGD.comm_prod L.c L.nabs (fun i => L.nabs_c i)
    have h2 : Commute L.nabs L.Drb := Formalism.FourierDecayAlt.P.RuleGD.comm_prod L.cb L.nabs (fun i => L.nabs_cb i)
    rw [map_one, one_mul, fn_G L (m_ζ L)]
    show L.nabs * (L.Dr * L.Drb * L.GG) = L.Dr * L.Drb * L.GG * L.nabs - L.Dr * L.Drb * L.ζ
    simp only [← mul_assoc]
    rw [h1.eq, mul_assoc L.Dr L.nabs L.Drb, h2.eq, ← mul_assoc L.Dr L.Drb L.nabs,
      mul_assoc (L.Dr * L.Drb) L.nabs L.GG, L.nabs_GG, mul_sub, ← mul_assoc (L.Dr * L.Drb) L.GG L.nabs]
  have hG := Formalism.FourierDecayAlt.P.gaugeConjugation A r L 1 L.G (TL.gI L) (G_gI L) (gI_G L) hfn hp hpb hnab hnabs
  have key : ∀ X X' : A, TL.gI L * X' * L.G = X → X * TL.gI L = TL.gI L * X' := by
    intro X X' h
    subst h
    rw [mul_assoc (TL.gI L * X') L.G (TL.gI L), G_gI, mul_one]
  have h1 := (hG (Y - 1)).1
  have h2 := (hG (Y - 1)).2.1
  have h3 := (hG (Y + 1)).2.2.1
  have h4 := (hG (Y + 1)).2.2.2
  rw [sub_add_cancel] at h1 h2
  rw [add_sub_cancel_right] at h3 h4
  exact ⟨key _ _ h1, key _ _ h2, key _ _ h3, key _ _ h4⟩

lemma star_inv {x xi y yi : A} (h : x * xi = 1) (h' : y * yi = 1) (hs : star x = y) : star xi = yi := by
  have h1 : star xi * y = 1 := by rw [← hs, ← star_mul, h, star_one]
  calc star xi = star xi * (y * yi) := by rw [h', mul_one]
    _ = star xi * y * yi := by rw [mul_assoc]
    _ = yi := by rw [h1, one_mul]

lemma star_prod {n : ℕ} (f g : Fin n → A) (h : ∀ i, star (f i) = g i) (hc : ∀ i j, g i * g j = g j * g i) :
    star (List.ofFn f).prod = (List.ofFn g).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h _) (fun i j => hc _ _), h 0]
    exact (Formalism.FourierDecayAlt.P.RuleGD.comm_prod (fun i => g i.succ) (g 0) (fun i => hc 0 i.succ)).symm

lemma star_D (hs : IsStarLevel L) (hc : ∀ l, star (L.c l) = L.cb l) : star L.D = L.Db := by
  have hs' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := hs
  have hDr : star L.Dr = L.Drb := star_prod L.c L.cb hc (fun i j => Formalism.FourierDecayAlt.P.RuleGD.fc L (m_cb L i) (m_cb L j))
  show star (L.Dr * L.ζ) = L.Drb * L.ζb
  rw [star_mul, hs'.1, hDr]
  exact Formalism.FourierDecayAlt.P.RuleGD.fns_Drb L (m_ζb L)

lemma star_fns [StarModule ℂ A] (hs : IsStarLevel L) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) {f : A} (hf : f ∈ L.fns) : star f ∈ L.fns := by
  have hs' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := hs
  have hzb : star L.ζb = L.ζ := by rw [← hs'.1, star_star]
  have hGG : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, hs'.1, hzb, ← algebraMap_star_comm, hs'.2.2]
  rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hf)
  · rw [hc]; exact m_cb L l
  · rw [hci]; exact m_cbi L l
  · rw [← hc, star_star]; exact m_c L l
  · rw [← hci, star_star]; exact m_ci L l
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hs'.1]; exact m_ζb L
    · rw [star_inv L.ζ_ζi L.ζb_ζbi hs'.1]; exact m_ζbi L
    · rw [hzb]; exact m_ζ L
    · rw [star_inv L.ζb_ζbi L.ζ_ζi hzb]; exact m_ζi L
    · rw [hGG]; exact m_GG L
    · rw [star_inv L.GG_GGi L.GG_GGi hGG]; exact m_GGi L

variable {P : M.Par} (d : Q.NFData P A)

lemma mem_D {b X : A} (hb : b ∈ bmon d) (hX : X ∈ hats d.L) : b * d.L.Di * X ∈ nfSpan d (hats d.L) 1 0 1 := by
  unfold nfSpan
  exact Submodule.subset_span ⟨b, hb, [X], rfl, by simpa using hX, by simp⟩

lemma mem_G {X : A} (hX : X ∈ hats d.L) : TL.gI d.L * X ∈ nfSpan d (hats d.L) 0 1 1 := by
  unfold nfSpan
  exact Submodule.subset_span ⟨1, one_mem _, [X], rfl, by simpa using hX, by simp⟩

lemma Di_mul_hatLetter_mem_normalFormSpan {X : A} (hX : X ∈ hats d.L) : d.L.Di * X ∈ nfSpan d (hats d.L) 1 0 1 := by
  unfold nfSpan
  exact Submodule.subset_span ⟨1, one_mem _, [X], rfl, by simpa using hX, by simp⟩

lemma ssn_comm (hR : d.Rel) (l : ℕ) {f : A} (hf : f ∈ d.L.fns) : Commute (ssn d l) f := by
  obtain ⟨-, -, hSS, -⟩ := hR
  have hff := of_fns d.L hf
  exact ((fm_comm d.L (mDrb d.L) hff).mul_left (fm_comm d.L (mDri d.L) hff)).mul_left
    (hSS l f (Set.mem_union_left _ (Set.mem_union_left _ hf)))

lemma bset_comm [StarModule ℂ A] (H : HatHyp d) {b : A} (hb : b ∈ bset d) {f : A} (hf : f ∈ d.L.fns) :
    Commute b f := by
  obtain ⟨-, hs, hR, -, hc, hci, -⟩ := H
  have hR' := hR
  obtain ⟨-, hRk, -⟩ := hR'
  have hff : f ∈ fm d.L := of_fns d.L hf
  unfold bset at hb
  rcases hb with ((hb | ⟨g, rfl⟩) | ⟨l, -, rfl⟩) | ⟨l, -, rfl⟩
  · rcases hb with rfl | rfl | rfl | rfl
    · exact fm_comm d.L (of_fns d.L (m_ζi d.L)) hff
    · exact fm_comm d.L (of_fns d.L (m_ζbi d.L)) hff
    · exact fm_comm d.L (mul_mem (mD d.L) (mDbi d.L)) hff
    · exact fm_comm d.L (mul_mem (mDb d.L) (mDi d.L)) hff
  · exact hRk g f (Set.mem_union_left _ hf)
  · exact ssn_comm d hR l hf
  · have h1 := (ssn_comm d hR l (star_fns d.L hs hc hci hf)).star_star
    rwa [star_star] at h1

lemma bset_star (H : HatHyp d) {b : A} (hb : b ∈ bset d) : star b ∈ bset d := by
  obtain ⟨-, hs, hR, -, hc, hci, -⟩ := H
  obtain ⟨hRs, -⟩ := hR
  have hs' : star d.L.ζ = d.L.ζb ∧ star d.L.nab = d.L.nabs ∧ star d.L.TT = d.L.TT := hs
  have hzb : star d.L.ζb = d.L.ζ := by rw [← hs'.1, star_star]
  have hD : star d.L.D = d.L.Db := star_D d.L hs hc
  have hDb : star d.L.Db = d.L.D := by rw [← hD, star_star]
  have hDi : star d.L.Di = d.L.Dbi := star_inv (D_Di d.L) (Db_Dbi d.L) hD
  have hDbi : star d.L.Dbi = d.L.Di := star_inv (Db_Dbi d.L) (D_Di d.L) hDb
  unfold bset at hb ⊢
  have m1 : ∀ x, x ∈ ({d.L.ζi, d.L.ζbi, d.L.D * d.L.Dbi, d.L.Db * d.L.Di} : Set A) →
      x ∈ ({d.L.ζi, d.L.ζbi, d.L.D * d.L.Dbi, d.L.Db * d.L.Di} ∪ Set.range d.κ ∪
        ssn d '' Set.Icc 1 (P.k - 1) ∪ (fun l => star (ssn d l)) '' Set.Icc 1 (P.k - 1)) :=
    fun x hx => Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hx))
  rcases hb with ((hb | ⟨g, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩
  · rcases hb with rfl | rfl | rfl | rfl
    · rw [star_inv d.L.ζ_ζi d.L.ζb_ζbi hs'.1]; exact m1 _ (by simp)
    · rw [star_inv d.L.ζb_ζbi d.L.ζ_ζi hzb]; exact m1 _ (by simp)
    · rw [star_mul, hDbi, hD, (fm_comm d.L (mDi d.L) (mDb d.L)).eq]; exact m1 _ (by simp)
    · rw [star_mul, hDi, hDb, (fm_comm d.L (mDbi d.L) (mD d.L)).eq]; exact m1 _ (by simp)
  · rw [hRs g]
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))
  · exact Set.mem_union_right _ ⟨l, hl, rfl⟩
  · rw [star_star]
    exact Set.mem_union_left _ (Set.mem_union_right _ ⟨l, hl, rfl⟩)

end star

theorem hat_den : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → (∀ X ∈ hats d.L, X * d.L.Di ∈ nfSpan d (hats d.L) 1 0 1 ∧ X * TL.gI d.L ∈ nfSpan d (hats d.L) 0 1 1) ∧ (∀ b ∈ bmon d, (∀ f ∈ d.L.fns, Commute b f) ∧ Commute b d.L.Di ∧ Commute b (TL.gI d.L) ∧ star b ∈ bmon d) ∧ Commute d.L.Di (TL.gI d.L) := by
  intro P A _ _ _ _ d H
  have hbf : ∀ b ∈ bmon d, ∀ f ∈ d.L.fns, Commute b f := by
    intro b hb f hf
    have hb' : b ∈ Submonoid.closure (bset d) := hb
    clear hb
    induction hb' using Submonoid.closure_induction with
    | mem x hx => exact bset_comm d H hx hf
    | one => exact Commute.one_left f
    | mul x y _ _ hx hy => exact hx.mul_left hy
  have hA : ∀ Y, d.L.Ahat Y ∈ hats d.L := fun Y => by simp [hats]
  have hR0 : ∀ Y, d.L.R0 Y ∈ hats d.L := fun Y => by simp [hats]
  have hAv : ∀ Y, d.L.Ahatv Y ∈ hats d.L := fun Y => by simp [hats]
  have hR0v : ∀ Y, d.L.R0v Y ∈ hats d.L := fun Y => by simp [hats]
  have hbm : d.L.Db * d.L.Di * d.L.ζbi ∈ bmon d :=
    mul_mem (Submonoid.subset_closure (by simp [bset])) (Submonoid.subset_closure (by simp [bset]))
  refine ⟨?_, ?_, fm_comm d.L (mDi d.L) (mgI d.L)⟩
  · intro X hX
    have hX' := hX
    rcases hX' with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
    · refine ⟨?_, ?_⟩
      · rw [Ahat_Di d.L]; exact Di_mul_hatLetter_mem_normalFormSpan d (hA _)
      · rw [(hats_gI d.L Y).1]; exact mem_G d (hA _)
    · refine ⟨?_, ?_⟩
      · rw [raising_mul_D_inv d.L]
        exact Submodule.sub_mem _ (Di_mul_hatLetter_mem_normalFormSpan d (hR0 _)) (Submodule.smul_mem _ _ (mem_D d hbm (hA _)))
      · rw [(hats_gI d.L Y).2.1]; exact mem_G d (hR0 _)
    · refine ⟨?_, ?_⟩
      · rw [← (v_Di d.L Y).1.eq]; exact Di_mul_hatLetter_mem_normalFormSpan d hX
      · rw [(hats_gI d.L Y).2.2.1]; exact mem_G d (hAv _)
    · refine ⟨?_, ?_⟩
      · rw [← (v_Di d.L Y).2.eq]; exact Di_mul_hatLetter_mem_normalFormSpan d hX
      · rw [(hats_gI d.L Y).2.2.2]; exact mem_G d (hR0v _)
  · intro b hb
    have hf := hbf b hb
    refine ⟨hf, comm_fm d.L hf (mDi d.L), comm_fm d.L hf (mgI d.L), ?_⟩
    have hb' : b ∈ Submonoid.closure (bset d) := hb
    clear hf hb
    induction hb' using Submonoid.closure_induction with
    | mem x hx => exact Submonoid.subset_closure (bset_star d H hx)
    | one => rw [star_one]; exact one_mem _
    | mul x y _ _ hx hy => rw [star_mul]; exact mul_mem hy hx

end GlobalTheory.HatNF.Den
