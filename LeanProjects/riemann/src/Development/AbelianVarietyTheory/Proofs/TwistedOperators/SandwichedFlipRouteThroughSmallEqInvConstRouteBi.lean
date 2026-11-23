import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem sand_restrictPol_comp (P : PolE G) {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z),
    restrictPol P (p.comp q) = (restrictPol P p).append (restrictPol P q)
  | _, .nil => rfl
  | _, .snoc a q => by
    show (restrictPol P (p.comp q), polOf P a) = ((restrictPol P p).append (restrictPol P q), polOf P a)
    rw [sand_restrictPol_comp P p q]

theorem sand_zip_append {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y}
    (d : p.Fam S) (u : p.Fam S') : ∀ {Z : Node} {q : Path T Y Z} (e : q.Fam S) (v : q.Fam S'),
    Path.Fam.zip φ (d.append e) (u.append v) = (Path.Fam.zip φ d u).append (Path.Fam.zip φ e v)
  | _, .nil, _, _ => rfl
  | _, .snoc a q, e, v => by
    show (Path.Fam.zip φ (d.append e.1) (u.append v.1), φ a e.2 v.2) =
      ((Path.Fam.zip φ d u).append (Path.Fam.zip φ e.1 v.1), φ a e.2 v.2)
    rw [sand_zip_append φ d u e.1 v.1]

theorem sand_restrictPol_congr {P P' : PolE G} {X : Node} : ∀ {Y : Node} (p : Path T X Y),
    (∀ b ∈ edges p, P b = P' b) → restrictPol P p = restrictPol P' p
  | _, .nil, _ => rfl
  | _, .snoc a p, h => by
    rw [edges_snoc] at h
    have h1 := sand_restrictPol_congr p fun b hb => h b (List.mem_append_left _ hb)
    have h2 := h (edgeOf a) (List.mem_append_right _ (List.mem_singleton_self _))
    show (restrictPol P p, polOf P a) = (restrictPol P' p, polOf P' a)
    rw [h1]
    congr 1
    cases a <;> simp only [polOf, edgeOf] at h2 ⊢ <;> first | rfl | exact h2

section Lin

variable (W : G.Weil) (M : Vol G)

theorem sand_liftConv_add {a : Arrow T} {f : Sch G a} {F F' : Fn G a.src} (h : LiftConv W M a f F)
    (h' : LiftConv W M a f F') : LiftConv W M a f (F + F') := fun x => by
  have e : (fun g => W.kerA a f g x * (F + F') g) = (fun g => W.kerA a f g x * F g) + (fun g => W.kerA a f g x * F' g) := by
    funext g; simp [mul_add]
  rw [e]; exact (h x).add (h' x)

theorem sand_liftConv_smul {a : Arrow T} {f : Sch G a} (c : ℂ) {F : Fn G a.src} (h : LiftConv W M a f F) :
    LiftConv W M a f (c • F) := fun x => by
  have e : (fun g => W.kerA a f g x * (c • F) g) = (fun g => c * (W.kerA a f g x * F g)) := by
    funext g; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e]; exact Integrable.const_mul (h x) c

theorem sand_liftP_zero {X Y : Node} (p : Path T X Y) (d : PureT G p) : liftP W M p d (0 : Fn G X) = 0 := by
  have := pathLift_smul W M (0 : ℂ) (0 : Fn G X) p d
  simpa only [zero_smul] using this

theorem sand_pathConv_zero {X : Node} : ∀ {Y : Node} (p : Path T X Y) (d : PureT G p), PathConv W M p d (0 : Fn G X)
  | _, .nil, _ => trivial
  | _, .snoc a p, d => ⟨sand_pathConv_zero p d.1, fun x => by
      rw [sand_liftP_zero]; simp only [Pi.zero_apply, mul_zero]; exact integrableOn_zero⟩

theorem sand_pathConv_add {X : Node} {F F' : Fn G X} : ∀ {Y : Node} (p : Path T X Y) (d : PureT G p),
    PathConv W M p d F → PathConv W M p d F' → PathConv W M p d (F + F')
  | _, .nil, _, _, _ => trivial
  | _, .snoc a p, d, h, h' => ⟨sand_pathConv_add p d.1 h.1 h'.1, by
      rw [pathLift_add W M p d.1 h.1 h'.1]; exact sand_liftConv_add W M h.2 h'.2⟩

theorem sand_pathConv_smul {X : Node} (c : ℂ) {F : Fn G X} : ∀ {Y : Node} (p : Path T X Y) (d : PureT G p),
    PathConv W M p d F → PathConv W M p d (c • F)
  | _, .nil, _, _ => trivial
  | _, .snoc a p, d, h => ⟨sand_pathConv_smul c p d.1 h.1, by
      rw [pathLift_smul]; exact sand_liftConv_smul W M c h.2⟩

theorem sand_liftP_sum {X Y : Node} (p : Path T X Y) (d : PureT G p) {ι : Type} (s : Finset ι) (f : ι → Fn G X)
    (h : ∀ k ∈ s, PathConv W M p d (f k)) :
    PathConv W M p d (∑ k ∈ s, f k) ∧ liftP W M p d (∑ k ∈ s, f k) = ∑ k ∈ s, liftP W M p d (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using sand_pathConv_zero W M p d, by simpa using sand_liftP_zero W M p d⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    have h0 := h a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨sand_pathConv_add W M p d h0 h1, by rw [pathLift_add W M p d h0 h1, h2]⟩

theorem sand_liftP_fsum {X Y : Node} (p : Path T X Y) (d : PureT G p) {ι : Type} (f : ι →₀ ℂ) (g : ι → ℂ → Fn G X)
    (h : ∀ k ∈ f.support, PathConv W M p d (g k (f k))) :
    PathConv W M p d (f.sum g) ∧ liftP W M p d (f.sum g) = f.sum fun k c => liftP W M p d (g k c) :=
  sand_liftP_sum W M p d f.support _ h

theorem sand_liftT_tensT {X Y : Node} (p : Path T X Y) (τi : PolT G p →₀ ℂ) (τf : TotT G p) (F : Fn G X) :
    liftT W M p (tensT W τi τf) F = τi.sum fun P c => τf.sum fun d c' =>
      (c * c') • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F := by
  unfold tensT
  simp only [Finsupp.sum, liftT_sum, liftT_single]

theorem sand_liftT_tensE {X Y : Node} (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) (F : Fn G X) :
    liftT W M p (tensE W p Q τ) F = Q.sum fun P c => τ.sum fun d c' =>
      (c * c') • liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P p)) F := by
  rw [tensE, sand_liftT_tensT, Finsupp.sum_mapDomain_index]
  · intro P; simp [Finsupp.sum]
  · intro P c c'; simp only [add_mul, add_smul, Finsupp.sum_add]

end Lin

theorem sand_sum_sandwich {X Y Z U : Node} {A : Path T X Y} {r : Path T Y Z} {B' : Path T Z U} (α : PureT G A) (σ : TotT G r)
    (β : PureT G B') {N : Type} [AddCommGroup N] [Module ℂ N] (k : ℂ) (g : PureT G ((A.comp r).comp B') → N) :
    ((σ.sum fun d c => Finsupp.single ((α.append d).append β) c : TotT G ((A.comp r).comp B')).sum fun x c' => (k * c') • g x) =
      σ.sum fun d c => (k * c) • g ((α.append d).append β) := by
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp [mul_add, add_smul])]
  exact Finsupp.sum_congr fun d _ => Finsupp.sum_single_index (by simp)

end GlobalTheory.FlipRun

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

open scoped TensorProduct

theorem sand_liftP_three (W : G.Weil) (M : Vol G) (P : PolE G) {X Y Z U : Node} (A : Path T X Y) (r : Path T Y Z)
    (B' : Path T Z U) (α : PureT G A) (d : PureT G r) (β : PureT G B') (F : Fn G X) :
    liftP W M ((A.comp r).comp B') (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) ((α.append d).append β) (restrictPol P ((A.comp r).comp B'))) F =
      liftP W M B' (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) β (restrictPol P B'))
        (liftP W M r (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P r)) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) := by
  rw [sand_restrictPol_comp, sand_restrictPol_comp, sand_zip_append, sand_zip_append, pathLift_comp, pathLift_comp]

theorem sand_vecAll_small {W : G.Weil} (ρ : RealMatch W) (e : AE D) (t : T) (i j : ℕ) (φ d : PureT G (routeSmall t i j))
    (h1 : IsLocVec W (.mu t i j) e (ρ.vT i j) φ.1.2 d.1.2) (h2 : IsLocVec W (.chi i j) e (ρ.vX i j) φ.2 d.2) :
    VecAll ρ e (routeSmall t i j) φ d := by
  show (True ∧ _) ∧ _
  exact ⟨⟨trivial, h1⟩, h2⟩

theorem sand_vecAll_big {W : G.Weil} (ρ : RealMatch W) (e : AE D) (t : T) (i j : ℕ) (φ d : PureT G (routeBig t i j))
    (h1 : IsLocVec W (.chi i (j + 1)) e (ρ.vX i (j + 1)) φ.1.2 d.1.2) (h2 : IsLocVec W (.mu t (i + 1) j) e (ρ.vT (i + 1) j) φ.2 d.2) :
    VecAll ρ e (routeBig t i j) φ d := by
  show (True ∧ _) ∧ _
  exact ⟨⟨trivial, h1⟩, h2⟩

theorem oneFlip_sandwich : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (c : ℂ), c ≠ 0 → CommutesWith W B ρ t ⟨i, hi⟩ ⟨j, hj⟩ c → M.Is t → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ (α : PureT G A) (β : PureT G Bp) (φA : PureT G A) (φB : PureT G Bp), GlobalTheory.FlipRun.VecAll ρ e A φA α → GlobalTheory.FlipRun.VecAll ρ e Bp φB β → ∀ (σs : TotT G (routeSmall t i j)) (σb : TotT G (routeBig t i j)) (Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ), (∀ w ∈ locPl G t, GlobalTheory.SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (Φ w)) → HasFlip B t ρ ⟨i, hi⟩ ⟨j, hj⟩ (depthAt G) Φ σb σs → ∀ F : Fn G (.grid 0 D.R.m), GlobalTheory.FlipRun.IsCuspListed W.θ _ F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, liftT W M _ (GlobalTheory.FlipRun.tensE W _ Q (((σs).sum fun d c => Finsupp.single (((α).append d).append (β)) c) : TotT G ((A.comp (routeSmall t i j)).comp Bp))) F = c⁻¹ • liftT W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) (((σb).sum fun d c => Finsupp.single (((α).append d).append (β)) c) : TotT G ((A.comp (routeBig t i j)).comp Bp))) F := by
  intro D T L sc G W M B ρ t i j hi hj c hc hcomm hM hC A Bp hA hBp e he α β φA φB hα hβ σs σb Φ hΦ hflip F hF Q
  classical
  obtain ⟨e', he', ⟨φ₁, φ₂, hs, -⟩, ⟨ψ₁, ψ₂, hb, -⟩⟩ := id hflip
  have hgS : OnGrid D.R.m t (routeSmall t i j) := onGrid_routeSmall t hi hj
  have hgB : OnGrid D.R.m t (routeBig t i j) := onGrid_routeBig t hi hj
  have hedA : ∀ b ∈ edges A, b ≠ .ex i (j + 1) ∧ b ≠ .theta (i + 1) j := by
    obtain ⟨i', j', h1, -, -, -, h5⟩ := edges_bound A hA
    obtain ⟨h6, -⟩ := Node.grid.inj h1
    intro b hb
    have := (h5 b hb).2.1
    constructor <;> rintro rfl <;> simp only [GlobalTheory.SplitFlip.Edge.tgt] at this <;> omega
  have hedB : ∀ b ∈ edges Bp, b ≠ .ex i (j + 1) ∧ b ≠ .theta (i + 1) j := by
    obtain ⟨i', j', -, -, -, -, h5⟩ := edges_bound Bp hBp
    intro b hb
    have h1 := (h5 b hb).1
    have h2 := (h5 b hb).2.2.2
    constructor <;> rintro rfl <;> simp only [GlobalTheory.SplitFlip.Edge.src] at h1 h2 <;> omega
  have hF' : ∀ P : PolE G, IsCuspListed W.θ _ (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) := fun P =>
    (pathConv_zip_fock M ρ t he hC A hA φA α hα (restrictPol P A) F hF).2
  have hcS : ∀ (P : PolE G) (P' : PolT G (routeSmall t i j)), ∀ d ∈ σs.support,
      PathConv W M _ (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) ∧
      IsCuspListed W.θ _ (liftP W M (routeSmall t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) :=
    fun P P' d hd => pathConv_zip_fock M ρ t he' hC _ hgS _ d (sand_vecAll_small ρ e' t i j (((), φ₁ d), φ₂ d) d (hs d hd).1 (hs d hd).2) P' _ (hF' P)
  have hcB : ∀ (P : PolE G) (P' : PolT G (routeBig t i j)), ∀ d ∈ σb.support,
      PathConv W M _ (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) ∧
      IsCuspListed W.θ _ (liftP W M (routeBig t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) :=
    fun P P' d hd => pathConv_zip_fock M ρ t he' hC _ hgB _ d (sand_vecAll_big ρ e' t i j (((), ψ₁ d), ψ₂ d) d (hb d hd).1 (hb d hd).2) P' _ (hF' P)
  have hbS : ∀ (P : PolE G) (P' : PolT G (routeSmall t i j)), ∀ d ∈ σs.support,
      PathConv W M Bp (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) β (restrictPol P Bp)) (liftP W M (routeSmall t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) :=
    fun P P' d hd => (pathConv_zip_fock M ρ t he hC Bp hBp φB β hβ (restrictPol P Bp) _ (hcS P P' d hd).2).1
  have hbB : ∀ (P : PolE G) (P' : PolT G (routeBig t i j)), ∀ d ∈ σb.support,
      PathConv W M Bp (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) β (restrictPol P Bp)) (liftP W M (routeBig t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) :=
    fun P P' d hd => (pathConv_zip_fock M ρ t he hC Bp hBp φB β hβ (restrictPol P Bp) _ (hcB P P' d hd).2).1
  have gen : ∀ (r : Path T (.grid i (j + 1)) (.grid (i + 1) j)) (σ : TotT G r) (P : PolE G) (k : ℂ),
      (∀ d ∈ σ.support, PathConv W M Bp (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) β (restrictPol P Bp))
        (liftP W M r (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P r)) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F))) →
      ((σ.sum fun d c => Finsupp.single ((α.append d).append β) c : TotT G ((A.comp r).comp Bp)).sum fun x c' =>
        (k * c') • liftP W M _ (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) x (restrictPol P ((A.comp r).comp Bp))) F) =
      liftP W M Bp (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) β (restrictPol P Bp))
        (σ.sum fun d s => (k * s) • liftP W M r (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P r)) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) := by
    intro r σ P k h
    refine (sand_sum_sandwich α σ β k _).trans ?_
    rw [(sand_liftP_fsum W M Bp _ σ _ fun d hd => sand_pathConv_smul W M _ Bp _ (h d hd)).2]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [sand_liftP_three, pathLift_smul]

  have hRB : ∀ (P' : PolE G) (q : ((Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) × PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank)), P' (.ex i (j + 1)) = q.1.2 → P' (.theta (i + 1) j) = q.2 →
      restrictPol P' (routeBig t i j) = q := fun P' q h1 h2 => Prod.ext (Prod.ext rfl h1) h2
  have perP : ∀ (P : PolE G) (k : ℂ) (a : ((Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) × PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank) →₀ ℂ), toTens a = matchLin ρ i j (P (.theta i j) ⊗ₜ P (.ex i j)) →
      ((σs.sum fun d c => Finsupp.single ((α.append d).append β) c : TotT G ((A.comp (routeSmall t i j)).comp Bp)).sum fun x c' =>
        (k * c') • liftP W M _ (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) x (restrictPol P ((A.comp (routeSmall t i j)).comp Bp))) F) =
      c⁻¹ • (a.sum fun q x => Finsupp.single (Function.update (Function.update P (.ex i (j + 1)) q.1.2) (.theta (i + 1) j) q.2) x).sum
        fun P' k' => ((σb.sum fun d c => Finsupp.single ((α.append d).append β) c : TotT G ((A.comp (routeBig t i j)).comp Bp)).sum
          fun x c' => ((k * k') * c') • liftP W M _ (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) x (restrictPol P' ((A.comp (routeBig t i j)).comp Bp))) F) := by
    intro P k a ha
    have hmatch : IsMatched B t ρ ⟨i, hi⟩ ⟨j, hj⟩ (tensT W (p := routeBig t i j) a σb)
        (tensT W (p := routeSmall t i j) (Finsupp.single (restrictPol P (routeSmall t i j)) 1) σs) := by
      refine ⟨a, _, σb, σs, depthAt G, Φ, ?_, fun w hw => ⟨le_rfl, hΦ w hw⟩, hflip, rfl, rfl⟩
      have hb' : toTens (P := PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid i j)).rank)
          (Q := PolF D (G.V (.grid i j)).rank (G.V (.grid (i + 1) j)).rank)
          (Finsupp.single (restrictPol P (routeSmall t i j)) 1) = P (.theta i j) ⊗ₜ P (.ex i j) := by
        erw [toTens, Finsupp.linearCombination_single, one_smul]; rfl
      have : (toTens a, toTens (P := PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid i j)).rank)
          (Q := PolF D (G.V (.grid i j)).rank (G.V (.grid (i + 1) j)).rank)
          (Finsupp.single (restrictPol P (routeSmall t i j)) 1)) ∈ ρ.rel i j := by
        rw [ha, hb']; exact matchLin_mem ρ i j _
      exact this
    obtain ⟨h1, h2, h3⟩ := hF' P
    have hTb : TotConv W M _ (tensT W (p := routeBig t i j) a σb) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) := fun x hx => by
      obtain ⟨d, hd, P', rfl⟩ := GlobalTheory.FlipRun.mem_support_tensT (W := W) (p := routeBig t i j) a σb x hx
      exact (hcB P P' d hd).1
    have hTs : TotConv W M _ (tensT W (p := routeSmall t i j) (Finsupp.single (restrictPol P (routeSmall t i j)) 1) σs) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) :=
      fun x hx => by
        obtain ⟨d, hd, P', rfl⟩ := GlobalTheory.FlipRun.mem_support_tensT (W := W) (p := routeSmall t i j) _ σs x hx
        exact (hcS P P' d hd).1
    have hcomm' : liftT W M (routeBig t i j) (tensT W (p := routeBig t i j) a σb) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) =
        c • liftT W M (routeSmall t i j) (tensT W (p := routeSmall t i j) (Finsupp.single (restrictPol P (routeSmall t i j)) 1) σs) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) :=
      hcomm M hM _ _ hmatch _ h1 h2 h3 hTb hTs
    rw [sand_liftT_tensT W M (routeBig t i j) a σb, sand_liftT_tensT, Finsupp.sum_single_index (by simp [Finsupp.sum])] at hcomm'
    try simp only [one_mul] at hcomm'
    rw [gen _ σs P k (hbS P _), Finsupp.sum_sum_index (fun _ => by simp [Finsupp.sum])
      (fun _ _ _ => by simp only [mul_add, add_mul, add_smul, Finsupp.sum_add])]
    rw [Finsupp.sum_congr (g2 := fun (q : ((Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) × PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank)) x => liftP W M Bp (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) β (restrictPol P Bp))
        (σb.sum fun d s => ((k * x) * s) • liftP W M (routeBig t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d q) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F))) ?_]
    · rw [← (sand_liftP_fsum W M Bp _ a _ fun q _ =>
        (sand_liftP_fsum W M Bp _ σb _ fun d hd => sand_pathConv_smul W M _ Bp _ (hbB P q d hd)).1).2]
      rw [show (a.sum fun (q : ((Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) × PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank)) x => σb.sum fun d s => ((k * x) * s) • liftP W M (routeBig t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d q) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) =
          k • (a.sum fun (q : ((Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) × PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank)) x => σb.sum fun d s => (x * s) • liftP W M (routeBig t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d q) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) by
        simp only [Finsupp.smul_sum, smul_smul, mul_assoc]]
      have hc2 : (a.sum fun (q : ((Unit × PolF D (G.V (.grid i (j + 1))).rank (G.V (.grid (i + 1) (j + 1))).rank) × PolF D (G.V (.grid (i + 1) (j + 1))).rank (G.V (.grid (i + 1) j)).rank)) x => σb.sum fun d s => (x * s) • liftP W M (routeBig t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d q) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) =
          c • σs.sum fun d s => s • liftP W M (routeSmall t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P (routeSmall t i j))) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) := hcomm'
      rw [hc2, show (σs.sum fun d s => (k * s) • liftP W M (routeSmall t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P (routeSmall t i j))) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F)) =
          k • σs.sum fun d s => s • liftP W M (routeSmall t i j) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P (routeSmall t i j))) (liftP W M A (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) α (restrictPol P A)) F) by
        simp only [Finsupp.smul_sum, smul_smul]]
      erw [pathLift_smul, pathLift_smul, pathLift_smul, smul_smul, smul_smul]
      congr 1
      field_simp
    · intro q _
      rw [Finsupp.sum_single_index (by simp [Finsupp.sum]), gen _ σb _ _ (hbB _ _)]
      rw [sand_restrictPol_congr (P' := P) A ?_, sand_restrictPol_congr (P' := P) Bp ?_, hRB _ q ?_ ?_]
      all_goals first
        | rfl
        | (intro b hb; rw [Function.update_of_ne (hedA b hb).2, Function.update_of_ne (hedA b hb).1])
        | (intro b hb; rw [Function.update_of_ne (hedB b hb).2, Function.update_of_ne (hedB b hb).1])
        | exact Function.update_self _ _ _
        | (rw [Function.update_of_ne (show GlobalTheory.SplitFlip.Edge.ex i (j + 1) ≠ .theta (i + 1) j by simp)]; exact Function.update_self _ _ _)
  rw [sand_liftT_tensE, sand_liftT_tensE, flipPolE,
    Finsupp.sum_sum_index (fun _ => by simp [Finsupp.sum]) (fun _ _ _ => by simp only [add_mul, add_smul, Finsupp.sum_add]),
    Finsupp.smul_sum]
  refine Finsupp.sum_congr fun P _ => ?_
  rw [Finsupp.sum_smul_index (fun _ => by simp [Finsupp.sum])]
  exact perP P (Q P) _ (toTens_surjective _).choose_spec

end GlobalTheory.FlipRun
