import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagClassConstancy.FlagOfInSFRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SubOneMulVecFix
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeviTens

noncomputable section

open Matrix Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.IdBlocks2.Conj

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add (x y z : Fin n → ℂ) : hJ ε x (y + z) = hJ ε x y + hJ ε x z := by
  simp [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_smul (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

theorem hJ_zero (x : Fin n → ℂ) : hJ ε x 0 = 0 := by simp [hJ]

theorem hJ_span_zero (x : Fin n → ℂ) (S : Set (Fin n → ℂ)) (h : ∀ y ∈ S, hJ ε x y = 0) :
    ∀ w ∈ Submodule.span ℂ S, hJ ε x w = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => exact hJ_zero ε x
  | add y z _ _ hy hz => rw [hJ_add, hy, hz, add_zero]
  | smul c y _ hy => rw [hJ_smul, hy, mul_zero]

theorem spanLt_mono (e : Fin r → Fin n → ℂ) {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b :=
  Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => lt_of_lt_of_le hc h)

theorem mem_spanLt (e : Fin r → Fin n → ℂ) {a : ℕ} (b : Fin r) (h : b.1 < a) : e b ∈ spanLt e a :=
  Submodule.subset_span ⟨b, h, rfl⟩

theorem sub_mem_of (e : Fin r → Fin n → ℂ) (m : Matrix (Fin n) (Fin n) ℂ)
    (hm : ∀ b : Fin r, m *ᵥ e b - e b ∈ spanLt e b.1) (a : ℕ) :
    ∀ w ∈ spanLt e (a + 1), m *ᵥ w - w ∈ spanLt e a := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    exact spanLt_mono e (Nat.lt_succ_iff.1 hb) (hm b)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add, show m *ᵥ y + m *ᵥ z - (y + z) = (m *ᵥ y - y) + (m *ᵥ z - z) by abel]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Matrix.mulVec_smul, ← smul_sub]
    exact Submodule.smul_mem _ c hy

theorem maps_of (e : Fin r → Fin n → ℂ) (m : Matrix (Fin n) (Fin n) ℂ)
    (hm : ∀ b : Fin r, m *ᵥ e b - e b ∈ spanLt e b.1) (a : ℕ) :
    ∀ w ∈ spanLt e a, m *ᵥ w ∈ spanLt e a := by
  intro w hw
  have h := sub_mem_of e m hm a w (spanLt_mono e (Nat.le_succ a) hw)
  have := Submodule.add_mem _ h hw
  rwa [sub_add_cancel] at this

variable (gg : ℕ) (E F : Fin r → Fin n → ℂ) (Z Z' : Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)

theorem conj_core (hgi : gi * g = 1) (hgi' : g * gi = 1)
    (hiso : ∀ x y, hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y)
    (hEg : ∀ b : Fin r, g *ᵥ E b - E b ∈ spanLt E b.1) (hEgi : ∀ b : Fin r, gi *ᵥ E b - E b ∈ spanLt E b.1)
    (hZ : g *ᵥ Z' - Z ∈ spanLt E r)
    (hFE : ∀ a b, hJ ε (F a) (E b) = if a = b then 1 else 0)
    (hFZ : ∀ a, hJ ε (F a) Z = 0) (hFZ' : ∀ a, hJ ε (F a) Z' = 0)
    (s : Matrix (Fin n) (Fin n) ℂ) :
    (InS E Z s → InS E Z' (gi * s * g) ∧ psiR ε gg E F Z' (gi * s * g) = psiR ε gg E F Z s) ∧
    (InN ε E Z s → InN ε E Z' (gi * s * g)) := by
  have hc : ∀ v, (gi * s * g - 1) *ᵥ v = gi *ᵥ (s *ᵥ (g *ᵥ v) - g *ᵥ v) := by
    intro v
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec v gi g, hgi, Matrix.one_mulVec]
  have hgiX : ∀ a, ∀ w ∈ spanLt E a, gi *ᵥ w ∈ spanLt E a := maps_of E gi hEgi

  have hiso' : ∀ x w, hJ ε (g *ᵥ x) w = hJ ε x (gi *ᵥ w) := by
    intro x w
    have := hiso x (gi *ᵥ w)
    rwa [Matrix.mulVec_mulVec, hgi', Matrix.one_mulVec] at this

  have hFlow : ∀ (a : Fin r) (w : Fin n → ℂ), w ∈ spanLt E a.1 → hJ ε (F a) w = 0 := by
    intro a w hw
    refine hJ_span_zero ε (F a) _ ?_ w hw
    rintro _ ⟨b, hb, rfl⟩
    rw [hFE, if_neg]
    intro h; subst h; simp at hb

  have hgF : ∀ (a : Fin r) (w : Fin n → ℂ), w ∈ spanLt E (a.1 + 1) → hJ ε (g *ᵥ F a) w = hJ ε (F a) w := by
    intro a w hw
    rw [hiso', show gi *ᵥ w = w + (gi *ᵥ w - w) by abel, hJ_add, hFlow a _ (sub_mem_of E gi hEgi a.1 w hw),
      add_zero]
  constructor
  · intro hs
    obtain ⟨hsE, hsZ⟩ := hs
    have hsX : ∀ a, ∀ w ∈ spanLt E (a + 1), s *ᵥ w - w ∈ spanLt E a := by
      intro a w hw
      exact sub_mem_of E s (fun b => by
        have := hsE b
        rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at this) a w hw
    have hsE' : ∀ b : Fin r, s *ᵥ E b - E b ∈ spanLt E b.1 := fun b => by
      have := hsE b
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at this
    have hsXX : ∀ a, ∀ w ∈ spanLt E a, s *ᵥ w ∈ spanLt E a := maps_of E s hsE'
    have hsZ' : s *ᵥ Z - Z ∈ spanLt E r := by rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at hsZ
    refine ⟨⟨fun a => ?_, ?_⟩, ?_⟩
    · rw [hc]
      refine hgiX _ _ ?_
      have h1 : g *ᵥ E a = E a + (g *ᵥ E a - E a) := by abel
      rw [h1, Matrix.mulVec_add, show s *ᵥ E a + s *ᵥ (g *ᵥ E a - E a) - (E a + (g *ᵥ E a - E a)) =
        (s *ᵥ E a - E a) + (s *ᵥ (g *ᵥ E a - E a) - (g *ᵥ E a - E a)) by abel]
      exact Submodule.add_mem _ (hsE' a) (by
        have := hsXX _ _ (hEg a)
        exact Submodule.sub_mem _ this (hEg a))
    · rw [hc]
      refine hgiX _ _ ?_
      have h1 : g *ᵥ Z' = Z + (g *ᵥ Z' - Z) := by abel
      rw [h1, Matrix.mulVec_add, show s *ᵥ Z + s *ᵥ (g *ᵥ Z' - Z) - (Z + (g *ᵥ Z' - Z)) =
        (s *ᵥ Z - Z) + (s *ᵥ (g *ᵥ Z' - Z) - (g *ᵥ Z' - Z)) by abel]
      exact Submodule.add_mem _ hsZ' (Submodule.sub_mem _ (hsXX _ _ hZ) hZ)
    ·
      have hroot : ∀ a, rootCoord ε E F Z' (gi * s * g) a = rootCoord ε E F Z s a := by
        intro a
        unfold rootCoord

        set N := nxt E Z a with hN
        set N' := nxt E Z' a with hN'
        have hxa : g *ᵥ N' - N ∈ spanLt E (a.1 + 1) := by
          by_cases h : a.1 + 1 < r
          · simp only [hN, hN', nxt, dif_pos h]
            exact hEg ⟨a.1 + 1, h⟩
          · simp only [hN, hN', nxt, dif_neg h]
            have : a.1 + 1 = r := by omega
            rw [this]; exact hZ
        have hsN : s *ᵥ N - N ∈ spanLt E (a.1 + 1) := by
          by_cases h : a.1 + 1 < r
          · simp only [hN, nxt, dif_pos h]
            exact hsE' ⟨a.1 + 1, h⟩
          · simp only [hN, nxt, dif_neg h]
            have : a.1 + 1 = r := by omega
            rw [this]; exact hsZ'
        have hFN : hJ ε (F a) N' = hJ ε (F a) N := by
          by_cases h : a.1 + 1 < r
          · simp only [hN, hN', nxt, dif_pos h]
          · simp only [hN, hN', nxt, dif_neg h]
            rw [hFZ, hFZ']
        have e1 : (gi * s * g) *ᵥ N' = gi *ᵥ (s *ᵥ (g *ᵥ N')) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rw [e1]
        have e2 : hJ ε (F a) (gi *ᵥ (s *ᵥ (g *ᵥ N'))) = hJ ε (g *ᵥ F a) (s *ᵥ (g *ᵥ N')) := (hiso' _ _).symm
        rw [e2]
        set x := g *ᵥ N' - N with hx
        have hgN : g *ᵥ N' = N + x := by rw [hx]; abel
        rw [hgN, Matrix.mulVec_add]
        have hdec : s *ᵥ N + s *ᵥ x = (N + x) + ((s *ᵥ N - N) + (s *ᵥ x - x)) := by abel
        have hbase : hJ ε (g *ᵥ F a) (N + x) = hJ ε (F a) N := by
          rw [← hgN, hiso, hFN]
        rw [hdec, hJ_add ε _ (N + x), hJ_add ε _ (s *ᵥ N - N), hbase, hgF a _ hsN,
          hgF a _ (spanLt_mono E (Nat.le_succ _) (hsX a.1 x hxa)), hFlow a _ (hsX a.1 x hxa), add_zero, ← hJ_add]
        congr 1
        abel
      unfold psiR
      simp only [hroot]
  · intro hs
    obtain ⟨⟨hsE, hsZ⟩, hsN⟩ := hs
    have hsE' : ∀ b : Fin r, s *ᵥ E b - E b ∈ spanLt E b.1 := fun b => by
      have := hsE b
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at this
    have hsXX : ∀ a, ∀ w ∈ spanLt E a, s *ᵥ w ∈ spanLt E a := maps_of E s hsE'
    have hsZ' : s *ᵥ Z - Z ∈ spanLt E r := by rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at hsZ
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · rw [hc]
      refine hgiX _ _ ?_
      have h1 : g *ᵥ E a = E a + (g *ᵥ E a - E a) := by abel
      rw [h1, Matrix.mulVec_add, show s *ᵥ E a + s *ᵥ (g *ᵥ E a - E a) - (E a + (g *ᵥ E a - E a)) =
        (s *ᵥ E a - E a) + (s *ᵥ (g *ᵥ E a - E a) - (g *ᵥ E a - E a)) by abel]
      exact Submodule.add_mem _ (hsE' a) (Submodule.sub_mem _ (hsXX _ _ (hEg a)) (hEg a))
    · rw [hc]
      refine hgiX _ _ ?_
      have h1 : g *ᵥ Z' = Z + (g *ᵥ Z' - Z) := by abel
      rw [h1, Matrix.mulVec_add, show s *ᵥ Z + s *ᵥ (g *ᵥ Z' - Z) - (Z + (g *ᵥ Z' - Z)) =
        (s *ᵥ Z - Z) + (s *ᵥ (g *ᵥ Z' - Z) - (g *ᵥ Z' - Z)) by abel]
      exact Submodule.add_mem _ hsZ' (Submodule.sub_mem _ (hsXX _ _ hZ) hZ)
    · rw [hc]
      refine hgiX _ _ ?_
      have hgy : ∀ a, hJ ε (E a) (g *ᵥ y) = 0 := by
        intro a
        have e : E a = g *ᵥ (gi *ᵥ E a) := by rw [Matrix.mulVec_mulVec, hgi', Matrix.one_mulVec]
        rw [e, hiso]

        have hm : gi *ᵥ E a ∈ spanLt E r := hgiX r _ (mem_spanLt E a a.2)
        have hy' : ∀ w ∈ spanLt E r, hJ ε w y = 0 := by
          intro w hw
          induction hw using Submodule.span_induction with
          | mem x hx => obtain ⟨b, -, rfl⟩ := hx; exact hy b
          | zero => simp [hJ]
          | add x z _ _ hx hz => simp only [hJ, star_add, add_dotProduct] at hx hz ⊢; rw [hx, hz, add_zero]
          | smul c x _ hx => simp only [hJ, star_smul, smul_dotProduct] at hx ⊢; rw [hx, smul_zero]
        exact hy' _ hm
      have := hsN (g *ᵥ y) hgy
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at this

end Formalism.L2.SG.Pf.IdBlocks2.Conj

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.IdBlocks2.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rat

variable {D : D7} (X : HidaSetting D)

def Xl (b : ℕ) : Submodule D.host.E (VS D).V := Submodule.span D.host.E (X.eX '' {c | c.1 < b})

theorem Xl_mono {a b : ℕ} (h : a ≤ b) : Xl X a ≤ Xl X b :=
  Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => lt_of_lt_of_le hc h)

theorem e_mem {b : ℕ} (c : Fin D.R.rS) (h : c.1 < b) : X.eX c ∈ Xl X b := Submodule.subset_span ⟨c, h, rfl⟩

theorem tri (G : Fin D.R.rS → (VS D).V) (a : ℕ) (h : ∀ c : Fin D.R.rS, c.1 < a → G c - X.eX c ∈ Xl X c.1) :
    Submodule.span D.host.E (G '' {c | c.1 < a}) = Xl X a := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    have : G c = X.eX c + (G c - X.eX c) := by abel
    rw [this]
    exact Submodule.add_mem _ (e_mem X c hc) (Xl_mono X (le_of_lt hc) (h c hc))
  · induction a with
    | zero =>
      rw [Xl, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      exact absurd hc (Nat.not_lt_zero _)
    | succ a ih =>
      have ih' := ih (fun c hc => h c (Nat.lt_succ_of_lt hc))
      have hmono : Submodule.span D.host.E (G '' {c | c.1 < a}) ≤
          Submodule.span D.host.E (G '' {c | c.1 < a + 1}) :=
        Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => Nat.lt_succ_of_lt hc)
      rw [Xl, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      by_cases hca : c.1 < a
      · exact hmono (ih' (e_mem X c hca))
      · have hce : c.1 = a := by
          have : c.1 < a + 1 := hc
          omega
        have hG : G c ∈ Submodule.span D.host.E (G '' {c | c.1 < a + 1}) := Submodule.subset_span ⟨c, hc, rfl⟩
        have hd : G c - X.eX c ∈ Submodule.span D.host.E (G '' {c | c.1 < a + 1}) := by
          have := h c hc
          rw [hce] at this
          exact hmono (ih' this)
        have : X.eX c = G c - (G c - X.eX c) := by abel
        show X.eX c ∈ _
        rw [this]
        exact Submodule.sub_mem _ hG hd

theorem inv_flag (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h : ∀ b : Fin D.R.rS, γ (X.eX b) - X.eX b ∈ Xl X b.1)
    (b : Fin D.R.rS) : γ.symm (X.eX b) - X.eX b ∈ Xl X b.1 := by
  have hsp := tri X (fun c => γ (X.eX c)) b.1 fun c _ => h c
  have hmap : ∀ w ∈ Xl X b.1, γ.symm w ∈ Xl X b.1 := by
    intro w hw
    rw [← hsp] at hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      simp only [LinearEquiv.symm_apply_apply]
      exact e_mem X c hc
    | zero => simp
    | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
    | smul c p _ hp => rw [map_smul]; exact Submodule.smul_mem _ c hp
  have := hmap _ (h b)
  rw [map_sub, LinearEquiv.symm_apply_apply] at this
  have h2 := Submodule.neg_mem _ this
  rwa [neg_sub] at h2

variable {X} {u u' : D.what₂.Word} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem inSF_of_isId (t : GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (ht : t.isId) :
    (∀ b : Fin D.R.rS, t.lin (X.eX b) - X.eX b ∈ Xl X b.1) ∧
      t.lin (X.zu u') - X.zu u ∈ Submodule.span D.host.E (Set.range X.eX) := by
  have h1 := Formalism.L2.SG.FourParts.isInS_of_isIdT ht
  have h2 := (Formalism.L2.SG.FourParts.isInS_mk (PI.InSClassConstW.inSFun_all _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩).1 h1
  have hfe : ∀ b, t.frame.fl.e b = t.lin ((X.Fu u').e b) := by
    intro b
    unfold GTerm.frame mapLF
    split_ifs with h
    · rfl
    · exact absurd t.rep.2.2.1 h
  have hfz : t.frame.fl.z = t.lin ((X.Fu u').z) := by
    unfold GTerm.frame mapLF
    split_ifs with h
    · rfl
    · exact absurd t.rep.2.2.1 h
  obtain ⟨he, hz⟩ := h2
  refine ⟨fun b => ?_, ?_⟩
  · have := he b
    change t.frame.fl.e b - (X.Fu u).e b ∈
      Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < b.1}) at this
    rw [hfe] at this
    rwa [X.Fu_e, X.Fu_e] at this
  · have := hz
    change t.frame.fl.z - (X.Fu u).z ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) at this
    rw [hfz] at this
    rwa [X.flagZVector, X.flagZVector, X.Fu_e] at this

end Rat

section Real

variable {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F)

theorem real_of_ratLink {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x γ) (y : (VS D).V) :
    uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (γ y)) := by
  obtain ⟨M, -, h1, -, h3⟩ := hx
  rw [h1 v, Formalism.L2.SG.Pf.rv_mulVec X v, h3]

theorem rv_span {S : Set (VS D).V} {w : (VS D).V} (hw : w ∈ Submodule.span D.host.E S) :
    rv X.B.I v (X.crd w) ∈ Submodule.span ℂ ((fun p => rv X.B.I v (X.crd p)) '' S) := by
  have h1 := Formalism.L2.SG.Pf.Vanish2.crd_span' X hw
  have h2 := Formalism.L2.SG.Pf.Vanish2.tr_span (X.B.I.φ v) (Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v)
    (Formalism.L2.SG.Pf.Vanish2.rv_smul' X.B.I v) h1
  rw [Set.image_image] at h2
  exact h2

theorem rv_crd_sub (a b : (VS D).V) :
    rv X.B.I v (X.crd (a - b)) = rv X.B.I v (X.crd a) - rv X.B.I v (X.crd b) := by
  rw [Formalism.L2.SG.Pf.Vanish2.crd_sub' X]
  exact map_sub (Formalism.L2.SG.Pf.Vanish2.rvHom X.B.I v) _ _

theorem hJ_iso' {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) (x y : Fin n → ℂ) : hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

end Real

theorem idOffConj_all {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)
    (what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)) :
    Formalism.L2.SG.TermOp.IdBlocks.IdOffConj (X.Fu u) (X.Fu u') what₂ rows' (X := X) := by
  intro _ t ht
  obtain ⟨hre, hrz⟩ := inSF_of_isId t ht
  have hx : RatLink X t.pt t.lin := t.rep.2.1
  have hxi : RatLink X t.pt⁻¹ t.lin⁻¹ := Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hx
  have hrei := inv_flag X t.lin hre

  have key : ∀ (v : InfinitePlace X.B.I.F) (s : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ),
      (InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) s →
        InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat (t.pt.1⁻¹ v) * s * uMat (t.pt.1 v)) ∧
          psiR (X.B.I.ε v) X.B.g (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u'))
            (uMat (t.pt.1⁻¹ v) * s * uMat (t.pt.1 v)) =
          psiR (X.B.I.ε v) X.B.g (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u))
            s) ∧
      (InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) s →
        InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))
          (uMat (t.pt.1⁻¹ v) * s * uMat (t.pt.1 v))) := by
    intro v s
    have hgi : uMat (t.pt.1⁻¹ v) * uMat (t.pt.1 v) = 1 := by simp [uMat]
    have hgi' : uMat (t.pt.1 v) * uMat (t.pt.1⁻¹ v) = 1 := by simp [uMat]
    refine conj_core (X.B.I.ε v) X.B.g _ _ _ _ _ _ hgi hgi' (hJ_iso' (X.B.I.ε v) (t.pt.1 v).2) ?_ ?_ ?_ ?_ ?_ ?_ s
    · intro b
      show uMat (t.pt.1 v) *ᵥ rv X.B.I v (X.crd (X.eX b)) - rv X.B.I v (X.crd (X.eX b)) ∈ _
      rw [real_of_ratLink X v hx, ← rv_crd_sub]
      have := rv_span X v (hre b)
      rw [Set.image_image] at this
      exact this
    · intro b
      have e1 : uMat (t.pt.1⁻¹ v) = uMat ((t.pt⁻¹).1 v) := rfl
      show uMat (t.pt.1⁻¹ v) *ᵥ rv X.B.I v (X.crd (X.eX b)) - rv X.B.I v (X.crd (X.eX b)) ∈ _
      rw [e1, real_of_ratLink X v hxi, ← rv_crd_sub]
      have := rv_span X v (hrei b)
      rw [Set.image_image] at this
      exact this
    · show uMat (t.pt.1 v) *ᵥ rv X.B.I v (X.crd (X.zu u')) - rv X.B.I v (X.crd (X.zu u)) ∈ _
      rw [real_of_ratLink X v hx, ← rv_crd_sub]
      have := rv_span X v hrz
      rw [← Set.range_comp] at this
      unfold spanLt
      rw [← Formalism.L2.SG.Pf.range_eq_image_lt]
      exact this
    · intro a b
      show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.eX b))) = _
      rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, Formalism.L2.SG.Pf.Level.hT_f_e X a b]
      by_cases hab : a = b
      · subst hab; simp
      · have : b ≠ a := fun h => hab h.symm
        simp [hab, this]
    · intro a
      show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.zu u))) = 0
      rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).2]
      simp
    · intro a
      show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.zu u'))) = 0
      rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u' a).2]
      simp
  have hm : ∀ (s : X.B.I.Ginf) v, uMat ((t.pt.1⁻¹ * s * t.pt.1) v) = uMat (t.pt.1⁻¹ v) * uMat (s v) * uMat (t.pt.1 v) := by
    intro s v; simp [uMat]
  refine ⟨fun s hs => ⟨fun v => ?_, ?_⟩, fun n hn v => ?_⟩
  · rw [show (fun a => rv X.B.I v (X.eR a)) = fun a => rv X.B.I v (X.eR a) from rfl]
    show InS _ _ (uMat ((t.pt.1⁻¹ * s * t.pt.1) v))
    rw [hm]
    exact ((key v (uMat (s v))).1 (hs v)).1
  · show psiInf X.B.I X.B.g X.eR X.fR (X.zR u') (t.pt.1⁻¹ * s * t.pt.1) = psiInf X.B.I X.B.g X.eR X.fR (X.zR u) s
    unfold psiInf
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hm]
    exact ((key v (uMat (s v))).1 (hs v)).2
  · show InN _ _ _ (uMat ((t.pt.1⁻¹ * n * t.pt.1) v))
    rw [hm]
    exact (key v (uMat (n v))).2 (hn v)

end Formalism.L2.SG.Pf.IdBlocks2.Conj

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.IdBlocks2.Lift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PI.SchurPlaces.Geo

theorem inv_maps {D : D7} (X : HidaSetting D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (h : ∀ b : Fin D.R.rS, γ (X.eX b) - X.eX b ∈ Conj.Xl X b.1) (a : ℕ) :
    ∀ w ∈ Conj.Xl X a, γ.symm w ∈ Conj.Xl X a := by
  have hsp := Conj.tri X (fun c => γ (X.eX c)) a fun c _ => h c
  intro w hw
  rw [← hsp] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    simp only [LinearEquiv.symm_apply_apply]
    exact Conj.e_mem X c hc
  | zero => simp
  | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | smul c p _ hp => rw [map_smul]; exact Submodule.smul_mem _ c hp

theorem idOffLift_all {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)
    (what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)) :
    Formalism.L2.SG.Pf.IdBlocks2.Geo.IdOffLift (X.Fu u) (X.Fu u') what₂ rows' (X := X) := by
  intro hu t ht v
  obtain ⟨hre, hrz⟩ := Conj.inSF_of_isId t ht
  have hx : RatLink X t.pt t.lin := t.rep.2.1
  have hxi : RatLink X t.pt⁻¹ t.lin⁻¹ := Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hx
  have hXtop : Conj.Xl X D.R.rS = Submodule.span D.host.E (Set.range X.eX) := by
    rw [Conj.Xl, Formalism.L2.SG.Pf.range_eq_image_lt]
  have hXinv : ∀ w ∈ Submodule.span D.host.E (Set.range X.eX),
      t.lin⁻¹ w ∈ Submodule.span D.host.E (Set.range X.eX) := by
    intro w hw
    rw [← hXtop] at hw ⊢
    exact inv_maps X t.lin hre _ w hw
  have hEX : ∀ c : Fin D.R.rS, X.eX c ∈ Submodule.span D.host.E (Set.range X.eX) :=
    fun c => Submodule.subset_span ⟨c, rfl⟩
  set ε := X.B.I.ε v with hε
  have hU : (uMat (t.pt.1 v))ᴴ * Formalism.REAL.Jm ε * uMat (t.pt.1 v) = Formalism.REAL.Jm ε := (t.pt.1 v).2
  have hgg : uMat (t.pt.1 v) * uMat (t.pt.1⁻¹ v) = 1 := by simp [uMat]
  have hγi : ∀ p, uMat (t.pt.1⁻¹ v) *ᵥ rvc X v p = rvc X v (t.lin⁻¹ p) :=
    fun p => Conj.real_of_ratLink X v hxi p
  have hmove : ∀ p y, hJ ε (rvc X v p) (uMat (t.pt.1 v) *ᵥ y) = hJ ε (rvc X v (t.lin⁻¹ p)) y := by
    intro p y
    rw [← hγi, ← hJ_unitary ε hU (uMat (t.pt.1⁻¹ v) *ᵥ rvc X v p) y, Matrix.mulVec_mulVec, hgg,
      Matrix.one_mulVec]
  have hperpE : ∀ b, ∀ p ∈ Submodule.span D.host.E (Set.range X.eX), hJ ε (rvc X v p) (X.wfr u' v b) = 0 :=
    fun b => orth_span X v (X.wfr u' v b) (by rintro _ ⟨a, rfl⟩; exact ((X.wfr_perp u' v b).1 a).1)

  have hyE : ∀ c b, hJ ε (rvc X v (X.eX c)) (uMat (t.pt.1 v) *ᵥ X.wfr u' v b) = 0 := by
    intro c b
    rw [hmove]
    exact hperpE b _ (hXinv _ (hEX c))
  have hyZ : ∀ b, hJ ε (rvc X v (X.zu u)) (uMat (t.pt.1 v) *ᵥ X.wfr u' v b) = 0 := by
    intro b
    rw [hmove]
    have hd : t.lin⁻¹ (X.zu u) - X.zu u' ∈ Submodule.span D.host.E (Set.range X.eX) := by
      have e : t.lin⁻¹ (X.zu u) - X.zu u' = -(t.lin⁻¹ (t.lin (X.zu u') - X.zu u)) := by
        rw [map_sub]
        have : t.lin⁻¹ (t.lin (X.zu u')) = X.zu u' := t.lin.symm_apply_apply _
        rw [this, neg_sub]
      rw [e]
      exact Submodule.neg_mem _ (hXinv _ hrz)
    have e2 : t.lin⁻¹ (X.zu u) = X.zu u' + (t.lin⁻¹ (X.zu u) - X.zu u') := by abel
    rw [e2, rvc_add, hJ_add_left, hperpE b _ hd, add_zero]
    exact (X.wfr_perp u' v b).2

  have hee : ∀ a c, hJ ε (rvc X v (X.eX a)) (rvc X v (X.eX c)) = 0 := fun a c => hJ_rvc_zero X v (X.ee a c)
  have hfe : ∀ a c, hJ ε (rvc X v (X.fY a)) (rvc X v (X.eX c)) = if c = a then 1 else 0 := by
    intro a c
    rw [hJ_symm, hJ_rvc, X.ef c a]
    split_ifs <;> simp
  have hze : ∀ c, hJ ε (rvc X v (X.zu u)) (rvc X v (X.eX c)) = 0 := by
    intro c
    rw [hJ_symm, hJ_rvc_zero X v (X.zu_orth u c).1, star_zero]
  have hwe : ∀ b c, hJ ε (X.wfr u v b) (rvc X v (X.eX c)) = 0 := by
    intro b c
    have h0 : hJ ε (rvc X v (X.eX c)) (X.wfr u v b) = 0 := ((X.wfr_perp u v b).1 c).1
    rw [hJ_symm, h0, star_zero]

  let y : Fin D.R.k → Fin X.B.I.n → ℂ := fun b => uMat (t.pt.1 v) *ᵥ X.wfr u' v b
  let ξ : Fin D.R.k → Fin X.B.I.n → ℂ := fun b => ∑ c, hJ ε (rvc X v (X.fY c)) (y b) • rvc X v (X.eX c)
  let A : Matrix (Fin D.R.k) (Fin D.R.k) ℂ := Matrix.of fun c b => hJ ε (X.wfr u v c) (y b)
  have hexp : ∀ b w, hJ ε w (y b - ξ b) =
      hJ ε w (y b) - ∑ c, hJ ε (rvc X v (X.fY c)) (y b) * hJ ε w (rvc X v (X.eX c)) := by
    intro b w
    simp only [ξ]
    rw [hJ_sub_right, hJ_sum_right]
    simp_rw [hJ_smul_right]
  have hdec : ∀ b, y b = ξ b + ∑ c, A c b • X.wfr u v c := by
    intro b
    have h1 := PI.SchurPlaces.wfrSpan D X u v (y b - ξ b) (fun a' => ⟨?_, ?_⟩) ?_
    rotate_left
    · show hJ ε (rvc X v (X.eX a')) _ = 0
      rw [hexp, hyE a' b]
      simp [hee]
    · show hJ ε (rvc X v (X.fY a')) _ = 0
      rw [hexp]
      simp_rw [hfe]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    · show hJ ε (rvc X v (X.zu u)) _ = 0
      rw [hexp, hyZ b]
      simp [hze]
    have hcoef : ∀ c, hJ ε (X.wfr u v c) (y b - ξ b) = A c b := by
      intro c
      rw [hexp]
      simp only [hwe, mul_zero, Finset.sum_const_zero, sub_zero]
      rfl
    have hsum : ∑ c, hJ ε (X.wfr u v c) (y b - ξ b) • X.wfr u v c = ∑ c, A c b • X.wfr u v c :=
      Finset.sum_congr rfl fun c _ => by rw [hcoef c]
    calc y b = ξ b + (y b - ξ b) := by abel
      _ = ξ b + ∑ c, A c b • X.wfr u v c := by rw [h1, hsum]

  have hξy : ∀ a b, hJ ε (ξ a) (y b) = 0 := by
    intro a b
    simp only [ξ]
    rw [hJ_sum_left]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hJ_smul_left, hyE c b, mul_zero]
  have hyξ : ∀ a b, hJ ε (y a) (ξ b) = 0 := by
    intro a b
    rw [hJ_symm]
    simp only [ξ]
    rw [hJ_sum_left]
    have : ∑ c, hJ ε ((hJ ε (rvc X v (X.fY c)) (y b)) • rvc X v (X.eX c)) (y a) = 0 :=
      Finset.sum_eq_zero fun c _ => by rw [hJ_smul_left, hyE c a, mul_zero]
    rw [this, star_zero]

  have hAA : Aᴴ * A = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply]
    calc ∑ c, star (A c a) * A c b = hJ ε (∑ c, A c a • X.wfr u v c) (y b) := by
          rw [hJ_sum_left]
          simp_rw [hJ_smul_left]
          rfl
      _ = hJ ε (y a) (y b) := by
          have e : y a = ξ a + ∑ c, A c a • X.wfr u v c := hdec a
          conv_rhs => rw [e]
          rw [hJ_add_left, hξy, zero_add]
      _ = _ := by
          simp only [y]
          rw [hJ_unitary ε hU]
          exact X.wfr_on u' v a b
  have hA : A ∈ Formalism.REAL.Kset (allPos D.R.k) := by
    refine ⟨?_, by rw [Formalism.L2.SG.Pf.IdBlocks2.HW.jm_allPos', Matrix.mul_one, Matrix.one_mul]⟩
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hAA
  refine ⟨A, hA, fun h hh hsupp x => ?_⟩
  have hS : t.pt.1⁻¹ * h * t.pt.1 ∈ X.SinfU u' :=
    ((Conj.idOffConj_all X u u' what₂ rows' hu t ht).1 h (hinf_le_sinf X u h hh)).1
  rw [PI.SchurPlaces.leviTens D X u' _ hS x]
  congr 1
  funext w
  have hm : uMat ((t.pt.1⁻¹ * h * t.pt.1) w) = uMat (t.pt.1⁻¹ w) * uMat (h w) * uMat (t.pt.1 w) := by
    simp [uMat]
  by_cases hw : w = v
  · subst hw
    rw [Function.update_self]
    congr 2

    set H := uMat (h w) with hHdef
    have hHE : ∀ c, H *ᵥ rvc X w (X.eX c) = rvc X w (X.eX c) :=
      fun c => hh w (X.eR c) (Or.inl (Or.inl ⟨c, rfl⟩))
    have hHU : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε := (h w).2
    have hHξ : ∀ b, H *ᵥ ξ b = ξ b := by
      intro b
      simp only [ξ]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [Matrix.mulVec_smul, hHE]
    have hEHw : ∀ c d, hJ ε (rvc X w (X.eX c)) (H *ᵥ X.wfr u w d) = 0 := by
      intro c d
      rw [← hHE c, hJ_unitary ε hHU]
      exact ((X.wfr_perp u w d).1 c).1
    have hξHw : ∀ a d, hJ ε (ξ a) (H *ᵥ X.wfr u w d) = 0 := by
      intro a d
      simp only [ξ]
      rw [hJ_sum_left]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hJ_smul_left, hEHw c d, mul_zero]
    funext a b
    show hJ ε (X.wfr u' w a) (uMat ((t.pt.1⁻¹ * h * t.pt.1) w) *ᵥ X.wfr u' w b) = _
    rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e1 : hJ ε (X.wfr u' w a) (uMat (t.pt.1⁻¹ w) *ᵥ (H *ᵥ (uMat (t.pt.1 w) *ᵥ X.wfr u' w b))) =
        hJ ε (y a) (H *ᵥ y b) := by
      rw [← hJ_unitary ε hU (X.wfr u' w a), Matrix.mulVec_mulVec (H *ᵥ _) (uMat (t.pt.1 w)), hgg,
        Matrix.one_mulVec]
    rw [e1]
    have e2 : H *ᵥ y b = ξ b + ∑ d, A d b • (H *ᵥ X.wfr u w d) := by
      conv_lhs => rw [hdec b]
      rw [Matrix.mulVec_add, hHξ, Matrix.mulVec_sum]
      congr 1
      exact Finset.sum_congr rfl fun d _ => by rw [Matrix.mulVec_smul]
    rw [e2, hJ_add_right, hyξ, zero_add, hJ_sum_right]
    have e3 : ∀ d, hJ ε (y a) (A d b • (H *ᵥ X.wfr u w d)) =
        A d b * ∑ c, star (A c a) * hJ ε (X.wfr u w c) (H *ᵥ X.wfr u w d) := by
      intro d
      rw [hJ_smul_right]
      congr 1
      rw [hdec a, hJ_add_left, hξHw, zero_add, hJ_sum_left]
      simp_rw [hJ_smul_left]
    simp_rw [e3]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.conjTranspose_apply]
    have hM : matW X.B.I (X.wfr u w) w h c d = hJ ε (X.wfr u w c) (H *ᵥ X.wfr u w d) := rfl
    rw [hM]
    ring
  · rw [Function.update_of_ne hw]
    have h1 : (t.pt.1⁻¹ * h * t.pt.1) w = 1 := by
      have : h w = 1 := hsupp w hw
      simp [this]
    have hmat : matW X.B.I (X.wfr u' w) w (t.pt.1⁻¹ * h * t.pt.1) = 1 := by
      funext a b
      show star (X.wfr u' w a) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε w) *ᵥ (uMat ((t.pt.1⁻¹ * h * t.pt.1) w) *ᵥ X.wfr u' w b)) =
        (1 : Matrix (Fin D.R.k) (Fin D.R.k) ℂ) a b
      rw [h1]
      have e : uMat (1 : Formalism.REAL.UJ (X.B.I.ε w)) = 1 := rfl
      rw [e]
      exact Formalism.L2.SG.Pf.IdBlocks2.UkEmb.one_mat _ _ (fun a b => X.wfr_on u' w a b) a b
    rw [hmat, (X.piLoc_type u' w).2.2.1.1.1]
    rfl

end Formalism.L2.SG.Pf.IdBlocks2.Lift

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem idOffConjC_holds : IdOffConjC :=
  fun _ X Y u u' => Formalism.L2.SG.Pf.IdBlocks2.Conj.idOffConj_all X u u' (Y.what₂ u) (Y.what₂ u')

theorem idOffLiftC_holds : IdOffLiftC :=
  fun _ X Y u u' => Formalism.L2.SG.Pf.IdBlocks2.Lift.idOffLift_all X u u' (Y.what₂ u) (Y.what₂ u')

theorem idCellOffC_holds_of_vol (hV : VolPosC) : IdCellOffC :=
  idCellOffC_of_conjLift nLamNinf_holds hV idOffConjC_holds idOffLiftC_holds

end Formalism.L2.SG.Pf
