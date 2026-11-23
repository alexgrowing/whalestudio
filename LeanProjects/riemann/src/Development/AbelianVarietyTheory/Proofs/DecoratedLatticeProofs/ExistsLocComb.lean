import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevPin
open GlobalTheory.FinPl (idAt MxAt grpAt SplitPt)

variable {D : D7}

theorem idAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, P w → P' w) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mxAt_of_half {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {m n : ℕ} (w : Mx D m n)
    (h : IsHalf (q.e + cA D q.e) w) : MxAt P w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  refine idAt_mono (fun w (hw : w = q.v) => hw ▸ hP) (GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_)
  rw [← h2]
  exact h i j

theorem exists_fold (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) {ι : Type} (c : ι → WO S T →₀ ℂ)
    (hc : ∀ i, ∀ w ∈ (c i).support, MxAt P w) (l : List ι) : ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, MxAt P w) ∧
      ∀ f, comb ψ S T c' f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun w hw => ?_, fun f => ?_⟩
    · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hw)
      exact fun i j => zero_mem _
    · rw [comb, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul,
        GlobalTheory.MixPer.heisO_zero]
      rfl
  | cons i l ih =>
    obtain ⟨c', h1, h2⟩ := ih
    obtain ⟨c'', h3, h4⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (c i) c'
    refine ⟨c'', fun w hw => ?_, fun f => by rw [h4, h2]; rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := h3 w hw
    exact fun a b => add_mem (hc i x hx a b) (h1 y hy a b)

theorem mxAt_cast {F : ℕ → HSp D} {T : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {s j : ℕ} (h : s = j) (x : WO (F s) T →₀ ℂ)
    (hx : ∀ w ∈ x.support, MxAt P w) : ∀ w ∈ (cast (congrArg (fun n => WO (F n) T →₀ ℂ) h) x).support, MxAt P w := by
  subst h
  exact hx

def conjHom {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) :
    GL (Fin N) k →* GL Y k where
  toFun g := ⟨F.γ * g.val * F.β, F.γ * (g⁻¹).val * F.β, by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc g.val,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, F.γβ], by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc (g⁻¹).val,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (1 : Matrix (Fin N) (Fin N) k) * F.β = 1
    rw [Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (g.val * h.val) * F.β = (F.γ * g.val * F.β) * (F.γ * h.val * F.β)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul])

theorem conj_iff {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y)
    (M : GL (Fin N) k) (x : GL Y k) : M.val = F.β * x.val * F.γ ↔ x = conjHom F M := by
  constructor
  · intro h
    refine Units.ext ?_
    change x.val = F.γ * M.val * F.β
    rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  · rintro rfl
    change M.val = F.β * (F.γ * M.val * F.β) * F.γ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, F.βγ, Matrix.one_mul, Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) : Subgroup G :=
  J.comap ((conjHom F).comp ρ)

theorem mem_frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) (g : G) :
    g ∈ frameSub ρ F J ↔ ∀ x : GL Y k, (ρ g).val = F.β * x.val * F.γ → x ∈ J := by
  constructor
  · intro h x hx
    rw [(conj_iff F _ x).1 hx]
    exact h
  · intro h
    exact h _ ((conj_iff F _ _).2 rfl)

theorem under_inj {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (hT : GlobalTheory.Core.Mi.IsTypePlaces Pg) {PP PP' : Formalism.L2.DIV.Pl D.host.E}
    (h : PP ∈ Pg) (h' : PP' ∈ Pg) (e : PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F)) : PP = PP' := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
    have := hT.1 PP h
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using this
  obtain ⟨Q, _, hu⟩ := hT.2 _ hm
  exact (hu PP ⟨h, rfl⟩).trans (hu PP' ⟨h', e.symm⟩).symm

end GlobalTheory.LevPin

namespace GlobalTheory.LevPin

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_locComb {a : XGeo D} {y : YRat a} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (S : SymData l.k l.s D.R.k) {N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)} {β : ∀ j, GL (Fin (Yc D j).rank) (Lev.EAf D)}
    {b : ∀ j, GA D (Yc D j)} {bas : ∀ j c, j + c = l.s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) l.k}
    (Y : LocY l y N β b bas) (ν : Measure l.k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (eg : ∀ j, WO (Yc D j) (Yc D (j + 1)) →₀ ℂ) (egT : WO (Yc D (l.s + 1)) D.sp.X' →₀ ℂ)
      (cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ),
      (∀ j a' (H : j + a' = l.s), (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) (eg j)
        ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      (ofSplit l.q).IsCombAt ψ (Y.FY (l.s + 1) 0 rfl) l.FT egT (S.T (Fin D.R.t)).PhiTop ∧
      (∀ j a' (H : j + 1 + a' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) (cg j)
        ((S.T (Fin D.R.t)).entry S.ψ ν j a' H 1 1)) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl) (cg l.s)
        (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX (l.s + 1) le_rfl) l.FM (cg (l.s + 1))
        ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t)))) ∧
      (∀ j, ∀ w ∈ (eg j).support, IsHalf (l.q.e + cA D l.q.e) w) ∧ (∀ j, ∀ w ∈ (cg j).support, IsHalf (l.q.e + cA D l.q.e) w) := by
  have keyE : ∀ j, ∃ c : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ a' (H : j + a' = l.s),
      (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) c ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j ≤ l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY j (l.s - j + 1) (by omega))
        (Y.FY (j + 1) (l.s - j) (by omega)) ((S.T (Fin D.R.t)).Phi j (l.s - j) (by omega))
      refine ⟨c, fun a' H => ?_, hc.1⟩
      obtain rfl : a' = l.s - j := by omega
      exact hc
    · exact ⟨0, fun a' H => by omega, by simp⟩
  choose eg heg sEg using keyE
  obtain ⟨egT, hegT⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY (l.s + 1) 0 rfl) l.FT
    (S.T (Fin D.R.t)).PhiTop
  obtain ⟨c₁, h₁⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl)
    (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
  obtain ⟨c₂, h₂⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX (l.s + 1) le_rfl) l.FM
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))
  have keyC : ∀ j, ∃ c : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ,
      (∀ c' (H : j + 1 + c' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) c
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)) ∧ (j = l.s → HEq c c₁) ∧ (j = l.s + 1 → HEq c c₂) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j < l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX j (by omega)) (l.FX (j + 1) (by omega))
        ((S.T (Fin D.R.t)).entry S.ψ ν j (l.s - j - 1) (by omega) 1 1)
      refine ⟨c, fun c'' H' => ?_, fun h => by omega, fun h => by omega, hc.1⟩
      obtain rfl : c'' = l.s - j - 1 := by omega
      exact hc
    · by_cases h1 : j = l.s
      · subst h1
        exact ⟨c₁, fun c' H => by omega, fun _ => HEq.rfl, fun h => by omega, h₁.1⟩
      · by_cases h2 : j = l.s + 1
        · subst h2
          exact ⟨c₂, fun c' H => by omega, fun h => by omega, fun _ => HEq.rfl, h₂.1⟩
        · exact ⟨0, fun c' H => by omega, fun h => (h1 h).elim, fun h => (h2 h).elim, by simp⟩
  choose cg k1 k2 k3 k4 using keyC
  refine ⟨eg, egT, cg, heg, hegT, k1, ?_, ?_, sEg, k4⟩
  · rw [eq_of_heq (k2 l.s rfl)]; exact h₁
  · rw [eq_of_heq (k3 (l.s + 1) rfl)]; exact h₂

end GlobalTheory.LevPin
