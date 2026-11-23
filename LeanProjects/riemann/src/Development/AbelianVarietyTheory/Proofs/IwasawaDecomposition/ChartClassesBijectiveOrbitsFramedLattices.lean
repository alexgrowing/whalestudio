import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section OrbF

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

theorem image_eq_iff_frStab {P : HeightOneSpectrum (𝓞 X.E)} (C : Set (Sp X.E n)) (g : ↥(GLint X.E n P)) :
    (fun v => g.1 v) '' C = C ↔ g ∈ frStab P C := by
  rw [mem_frStab]
  constructor
  · intro e v
    constructor
    · intro hv
      rw [← e] at hv
      obtain ⟨u, hu, huv⟩ := hv
      rwa [← g.1.injective huv]
    · intro hv
      rw [← e]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h u).2 hu
    · intro hv
      refine ⟨g.1.symm v, (h _).1 ?_, LinearEquiv.apply_symm_apply g.1 v⟩
      rw [LinearEquiv.apply_symm_apply]
      exact hv

def frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) : FrmG Λ Θ :=
  (g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, cutQ_grp_le _ _ g.2.2.2⟩)

theorem ya_frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) (q : PtY ST SG Q y) :
    (ya Λ Θ (frLift Λ Θ C D g) q).1.1 = g • q.1.1 := rfl

end OrbF

end GlobalTheory.Mem.Col2.ChEx

namespace GlobalTheory.Mem.Col2.ChEx

theorem clsF_bij : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  intro X n ST SG Q y β _ _ Λ Θ p₀ pref cq _ hact hdet hsur hnorm c₀ p hp
  constructor
  · rintro ⟨c, h⟩ ⟨c', h'⟩ e
    obtain ⟨h1, h2, h3⟩ := (hp c).1 h
    obtain ⟨h1', h2', h3'⟩ := (hp c').1 h'
    apply Subtype.ext
    show c = c'
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 (Quotient.exact' e)
    have hb : bar (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = bar (rp Λ Θ p₀ pref c') :=
      (bar_ya_eq_iff _ _ _ _).2 fun w => by rw [h2']; exact (mem_chG.1 g.2.1.2).2 w
    have hq : cq (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = cq (rp Λ Θ p₀ pref c') := by
      funext P
      rw [hact, h3']
      exact (image_eq_iff_frStab _ _).2 ((mem_cutQ_grp.1 g.2.2.2).2 P)
    have e2 : ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c') = rp Λ Θ p₀ pref c :=
      hdet _ _ (by rw [ya_frLift]; exact hg) (hb.trans (h2'.trans h2.symm)) (hq.trans (h3'.trans h3.symm))
    have e3 := cl_ya Λ Θ p₀ pref c₀.1 (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')
    rw [e2] at e3
    have e4 := cl_rp Λ Θ p₀ pref c
    have e5 := cl_rp Λ Θ p₀ pref c'
    have t : ∀ b b' : β, b = b' → ∀ q : PtY ST SG Q y, (stR Λ Θ p₀ pref).cl b q = (stR Λ Θ p₀ pref).cl b' q := by
      rintro b _ rfl q
      rfl
    exact e4.symm.trans ((t _ _ h1 _).trans (e3.trans ((t _ _ h1' _).symm.trans e5)))
  · intro z
    induction z using Quotient.inductionOn' with
    | h d =>
      obtain ⟨r', h1, h2, h3⟩ := hsur (rp Λ Θ p₀ pref c₀) d
      obtain ⟨hb, hq⟩ := hnorm c₀.1 _ _ h2.symm h3.symm
      rw [cl_rp] at hb hq
      refine ⟨⟨(stR Λ Θ p₀ pref).cl c₀.1 r', (hp _).2 ⟨rfl, hb.symm, hq.symm⟩⟩, ?_⟩
      obtain ⟨g, hg⟩ := exists_ya Λ Θ p₀ pref c₀.1 r'
      rw [hg] at hb hq
      have hb' : bar (ya (Λ c₀.1) (Θ c₀.1) g r') = bar r' := hb.symm.trans h2.symm
      have hq' : cq (ya (Λ c₀.1) (Θ c₀.1) g r') = cq r' := hq.symm.trans h3.symm
      rw [bar_ya_eq_iff, h2] at hb'
      have hC : ∀ P : Q, g.2.2.1 P ∈ frStab P.1 (cq (rp Λ Θ p₀ pref c₀) P) := fun P => by
        rw [← h3, ← image_eq_iff_frStab]
        have := congrFun hq' P
        rwa [hact] at this
      let g' : UF X.E n × chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀)) × (cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀))).grp :=
        (g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, hb'⟩⟩, ⟨g.2.2.1, mem_cutQ_grp.2 ⟨g.2.2.2, hC⟩⟩)
      refine Quotient.sound' (MulAction.orbitRel_apply.2 ⟨g', ?_⟩)
      show g' • d = (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl c₀.1 r')).1.1
      rw [hg, ← h1]
      rfl

end GlobalTheory.Mem.Col2.ChEx
