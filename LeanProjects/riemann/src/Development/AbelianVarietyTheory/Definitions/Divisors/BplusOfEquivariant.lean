import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def levCol (L : LevCh D T) (t : T) (j : ℕ) : Subgroup (GL (Fin (columnBlock L (j + 1)).sp.rank) (Lev.EAf D)) :=
  if h : j + 1 < D.R.m then
    cast (by rw [colY_lt L h])
      (Formalism.L2.DIV.lev D.sp.cm (Yc D (j + 1)).gram (L.βY (j + 1)) (L.datYt t (j + 1) L.triv))
  else cast (by rw [columnBlock, if_neg h]) (Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t))

theorem levCol_lt (L : LevCh D T) (t : T) {j : ℕ} (h : j + 1 < D.R.m) : HEq (levCol L t j)
    (Formalism.L2.DIV.lev D.sp.cm (Yc D (j + 1)).gram (L.βY (j + 1)) (L.datYt t (j + 1) L.triv)) := by
  rw [levCol, dif_pos h]; exact cast_heq _ _

theorem levCol_top (L : LevCh D T) (t : T) {j : ℕ} (h : ¬ j + 1 < D.R.m) : HEq (levCol L t j)
    (Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
  rw [levCol, dif_neg h]; exact cast_heq _ _

def levJ (G : GridData L sc) (t : T) : ∀ X : Node, Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))
  | .grid i 0 => G.levCong (.grid i 0)
  | .grid 0 (j + 1) => levCol L t j
  | .grid (i + 1) (j + 1) => G.levMax (.grid (i + 1) (j + 1))
  | .core i => G.levCong (.core i)
  | .top 0 => G.levCong (.top 0)
  | .top (j + 1) => G.levMax (.top (j + 1))

theorem levJ_row (G : GridData L sc) (t : T) (i : ℕ) : levJ G t (.grid i 0) = G.levCong (.grid i 0) := by
  cases i <;> rfl

structure Vol (G : GridData L sc) where

  ν : ∀ X : Node, Measure (GA D (G.V X))

  fd : ∀ X : Node, Set (GA D (G.V X))

  νN : Measure (NFlag (G.V (.grid D.R.m 0)) G.besTop.e)

  fdN : Set (NFlag (G.V (.grid D.R.m 0)) G.besTop.e)

variable {G : GridData L sc}

def Vol.IsAt (M : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))) : Prop :=
  if X.neg D.R.m = 0 then IsMeasDef (G.V X) K (M.ν X) (M.fd X) else Lev.IsMeasFD (G.V X) K (M.ν X) (M.fd X)

theorem Vol.IsAt.haar_fund {M : Vol G} {X : Node} {K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))} (h : M.IsAt X K) :
    (M.ν X).IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V X)) (M.fd X) (M.ν X) := by
  unfold Vol.IsAt at h
  split_ifs at h <;> exact ⟨h.1.1, h.2⟩

structure Vol.IsRow (M : Vol G) : Prop where

  row : ∀ i, i ≤ D.R.m → M.IsAt (.grid i 0) (G.levCong (.grid i 0))

  top : M.IsAt (.top 0) G.Kplus

  unip : GlobalTheory.Per.IsUnitN _ G.besTop.e M.νN M.fdN

structure Vol.Is (M : Vol G) (t : T) : Prop where

  vtx : ∀ X : Node, X.InRange D.R.m → M.IsAt X (levJ G t X)

  unip : GlobalTheory.Per.IsUnitN _ G.besTop.e M.νN M.fdN

theorem Vol.Is.isRow {M : Vol G} {t : T} (h : M.Is t) : M.IsRow :=
  ⟨fun i hi => levJ_row G t i ▸ h.vtx (.grid i 0) ⟨hi, Nat.zero_le _⟩, h.vtx (.top 0) (Nat.zero_le _), h.unip⟩

theorem node_isV (G : GridData L sc) {μ0 : T} (hL : L.Is μ0) {X : Node} (h : X.InRange D.R.m) :
    (G.node X).IsV (X.rank D) (X.neg D.R.m) := by
  by_cases h0 : ∃ j, X = .grid 0 j
  · obtain ⟨j, rfl⟩ := h0
    exact colY_isV D T L μ0 hL j h.2
  · exact G.isV h fun j e => h0 ⟨j, e⟩

theorem levJ_open_compact (G : GridData L sc) {μ0 : T} (hL : L.Is μ0) (t : T) {X : Node} (h : X.InRange D.R.m) :
    IsOpen (((levJ G t X).comap (Lev.finE (G.V X)) : Subgroup (GA D (G.V X))) : Set (GA D (G.V X))) ∧
      IsCompact ((Lev.levA (G.V X) (levJ G t X) : Subgroup (GA D (G.V X))) : Set (GA D (G.V X))) := by
  have hc := congLev_open_compact _ (node_isV G hL h).sd.1 (G.pl.modul_ne_bot sc)
  have hm := congLev_open_compact _ (node_isV G hL h).sd.1 (𝔪 := ⊤) top_ne_bot
  have key : ∀ (Y : LSp D) (V : HSp D) Λ β (d : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
      (K : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))), Y = ⟨V, Λ⟩ → HEq K (Formalism.L2.DIV.lev D.sp.cm V.gram β d) →
      IsOpen ((K.comap (Lev.finE Y.sp) : Subgroup (GA D Y.sp)) : Set (GA D Y.sp)) ∧
        IsCompact ((Lev.levA Y.sp K : Subgroup (GA D Y.sp)) : Set (GA D Y.sp)) := by
    rintro _ V Λ β d K rfl e
    obtain rfl := eq_of_heq e
    exact ⟨GlobalTheory.ParahoricCompact.isOpen_comap_lev V β d, GlobalTheory.ParahoricCompact.isCompact_levG V β d⟩
  rcases X with ⟨_ | i, _ | j⟩ | i | _ | j
  any_goals first | exact hc | exact hm
  by_cases hj : j + 1 < D.R.m
  · exact key _ _ _ _ _ _ (colY_lt L hj) (levCol_lt L t hj)
  · exact key _ _ _ _ _ _ (if_neg hj) (levCol_top L t hj)

theorem exists_vol (G : GridData L sc) {μ0 : T} (hL : L.Is μ0) (t : T) : ∃ M : Vol G, M.Is t := by
  have H : ∀ X : Node, ∃ μ 𝓕, X.InRange D.R.m → if X.neg D.R.m = 0 then IsMeasDef (G.V X) (levJ G t X) μ 𝓕
      else Lev.IsMeasFD (G.V X) (levJ G t X) μ 𝓕 := fun X => by
    by_cases h : X.InRange D.R.m
    · obtain ⟨μ, 𝓕, e⟩ := exists_meas _ (node_isV G hL h).sigOK (fun τ => congrArg Prod.snd ((node_isV G hL h).sig τ)) _
        (levJ_open_compact G hL t h)
      exact ⟨μ, 𝓕, fun _ => e⟩
    · exact ⟨0, ∅, fun h' => absurd h' h⟩
  choose ν fd hν using H
  obtain ⟨νN, fdN, hN⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D _ _ _ G.besTop.e_iso
  exact ⟨⟨ν, fd, νN, fdN⟩, hν, hN⟩

abbrev Sch (G : GridData L sc) (a : Arrow T) : Type := WO (G.pS a.pair) (G.pT a.pair) → ℂ

abbrev Fn (G : GridData L sc) (X : Node) : Type := GA D (G.V X) → ℂ

variable (W : G.Weil) (M : Vol G)

def liftA (a : Arrow T) (f : Sch G a) (F : Fn G a.src) : Fn G a.tgt :=
  Lift.liftInt (M.ν a.src) (M.fd a.src) (fun h g f => W.kerA a f g h) f F

theorem liftA_apply (a : Arrow T) (f : Sch G a) (F : Fn G a.src) (h : GA D (G.V a.tgt)) :
    liftA W M a f F h = ∫ g in M.fd a.src, W.kerA a f g h * F g ∂M.ν a.src := rfl

def LiftConv (a : Arrow T) (f : Sch G a) (F : Fn G a.src) : Prop :=
  ∀ h, IntegrableOn (fun g => W.kerA a f g h * F g) (M.fd a.src) (M.ν a.src)

theorem liftA_smul (a : Arrow T) (f : Sch G a) (c : ℂ) (F : Fn G a.src) :
    liftA W M a f (c • F) = c • liftA W M a f F := by
  funext h
  simp only [liftA_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem liftA_add {a : Arrow T} {f : Sch G a} {F F' : Fn G a.src} (h : LiftConv W M a f F) (h' : LiftConv W M a f F') :
    liftA W M a f (F + F') = liftA W M a f F + liftA W M a f F' := by
  funext x
  simp only [liftA_apply, Pi.add_apply, mul_add]
  exact integral_add (h x) (h' x)

inductive Path (T : Type) (X : Node) : Node → Type

  | nil : Path T X X

  | snoc (a : Arrow T) (p : Path T X a.src) : Path T X a.tgt

namespace Path

variable {X Y Z : Node}

abbrev one (a : Arrow T) : Path T a.src a.tgt := .snoc a .nil

noncomputable def comp (p : Path T X Y) : ∀ {Z : Node}, Path T Y Z → Path T X Z
  | _, .nil => p
  | _, .snoc a q => .snoc a (comp p q)

noncomputable def arrows : ∀ {Y : Node}, Path T X Y → List (Arrow T)
  | _, .nil => []
  | _, .snoc a p => p.arrows ++ [a]

noncomputable def Fam (S : Arrow T → Type) : ∀ {Y : Node}, Path T X Y → Type
  | _, .nil => Unit
  | _, .snoc a p => p.Fam S × S a

noncomputable def Fam.append {S : Arrow T → Type} {p : Path T X Y} (d : p.Fam S) :
    ∀ {Z : Node} {q : Path T Y Z}, q.Fam S → (p.comp q).Fam S
  | _, .nil, _ => d
  | _, .snoc _ _, e => (Fam.append d e.1, e.2)

noncomputable def Fam.zip {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) :
    ∀ {Y : Node} {p : Path T X Y}, p.Fam S → p.Fam S' → p.Fam S''
  | _, .nil, _, _ => ()
  | _, .snoc a _, d, e => (Fam.zip φ d.1 e.1, φ a d.2 e.2)

noncomputable def Fam.All {S : Arrow T → Type} (P : ∀ a, S a → Prop) : ∀ {Y : Node} {p : Path T X Y}, p.Fam S → Prop
  | _, .nil, _ => True
  | _, .snoc a _, d => Fam.All P d.1 ∧ P a d.2

end Path

noncomputable def rowPath (T : Type) (j : ℕ) : ∀ n, Path T (.grid 0 j) (.grid n j)
  | 0 => .nil
  | n + 1 => .snoc (.right n j) (rowPath T j n)

noncomputable def downPath (t : T) (i : ℕ) : ∀ n, Path T (.grid i n) (.grid i 0)
  | 0 => .nil
  | n + 1 => (Path.one (.down t i n)).comp (downPath t i n)

def givenPath (t : T) (m : ℕ) : Path T (.grid 0 m) (.grid m 0) := (downPath t 0 m).comp (rowPath T 0 m)

def oppPath (t : T) (m : ℕ) : Path T (.grid 0 m) (.grid m 0) := (rowPath T m m).comp (downPath t m m)

noncomputable def rowFam {S : Arrow T → Type} (j : ℕ) : ∀ n, (∀ i : Fin n, S (.right i j)) → (rowPath T j n).Fam S
  | 0, _ => ()
  | n + 1, f => (rowFam j n fun i => f i.castSucc, f (Fin.last n))

noncomputable def downFam {S : Arrow T → Type} (t : T) (i : ℕ) : ∀ n, (∀ j : Fin n, S (.down t i j)) → (downPath t i n).Fam S
  | 0, _ => ()
  | n + 1, f => Path.Fam.append (p := Path.one (.down t i n)) ((), f (Fin.last n)) (downFam t i n fun j => f j.castSucc)

variable {X Y Z : Node}

abbrev PureT (G : GridData L sc) (p : Path T X Y) : Type := p.Fam (Sch G)

abbrev TotT (G : GridData L sc) (p : Path T X Y) : Type := PureT G p →₀ ℂ

abbrev PolT (G : GridData L sc) (p : Path T X Y) : Type :=
  p.Fam fun a => PolF D (G.pT a.pair).rank (G.pS a.pair).rank

noncomputable def liftP : ∀ {Y : Node} (p : Path T X Y), PureT G p → Fn G X → Fn G Y
  | _, .nil, _, F => F
  | _, .snoc a p, d, F => liftA W M a d.2 (liftP p d.1 F)

noncomputable def PathConv : ∀ {Y : Node} (p : Path T X Y), PureT G p → Fn G X → Prop
  | _, .nil, _, _ => True
  | _, .snoc a p, d, F => PathConv p d.1 F ∧ LiftConv W M a d.2 (liftP W M p d.1 F)

def liftT (p : Path T X Y) (τ : TotT G p) (F : Fn G X) : Fn G Y := τ.sum fun d c => c • liftP W M p d F

def TotConv (p : Path T X Y) (τ : TotT G p) (F : Fn G X) : Prop := ∀ d ∈ τ.support, PathConv W M p d F

def tensT {p : Path T X Y} (τi : PolT G p →₀ ℂ) (τf : TotT G p) : TotT G p :=
  τi.sum fun P c => τf.sum fun d c' =>
    Finsupp.single (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) (c * c')

theorem pathLift_comp (p : Path T X Y) (d : PureT G p) (F : Fn G X) : ∀ {Z : Node} (q : Path T Y Z) (e : PureT G q),
    liftP W M (p.comp q) (d.append e) F = liftP W M q e (liftP W M p d F)
  | _, .nil, _ => rfl
  | _, .snoc a q, e => congrArg (liftA W M a e.2) (pathLift_comp p d F q e.1)

theorem pathConv_comp (p : Path T X Y) (d : PureT G p) (F : Fn G X) : ∀ {Z : Node} (q : Path T Y Z) (e : PureT G q),
    PathConv W M (p.comp q) (d.append e) F ↔ PathConv W M p d F ∧ PathConv W M q e (liftP W M p d F)
  | _, .nil, _ => (and_iff_left trivial).symm
  | _, .snoc a q, e => by
    show PathConv W M (p.comp q) (d.append e.1) F ∧ LiftConv W M a e.2 (liftP W M (p.comp q) (d.append e.1) F) ↔ _
    rw [pathConv_comp p d F q e.1, pathLift_comp, and_assoc]
    rfl

theorem pathLift_smul (c : ℂ) (F : Fn G X) : ∀ {Y : Node} (p : Path T X Y) (d : PureT G p),
    liftP W M p d (c • F) = c • liftP W M p d F
  | _, .nil, _ => rfl
  | _, .snoc a p, d => (congrArg (liftA W M a d.2) (pathLift_smul c F p d.1)).trans (liftA_smul W M a d.2 c _)

theorem pathLift_add {F F' : Fn G X} : ∀ {Y : Node} (p : Path T X Y) (d : PureT G p), PathConv W M p d F → PathConv W M p d F' →
    liftP W M p d (F + F') = liftP W M p d F + liftP W M p d F'
  | _, .nil, _, _, _ => rfl
  | _, .snoc a p, d, h, h' => (congrArg (liftA W M a d.2) (pathLift_add p d.1 h.1 h'.1)).trans (liftA_add W M h.2 h'.2)

theorem liftT_single (p : Path T X Y) (d : PureT G p) (c : ℂ) (F : Fn G X) :
    liftT W M p (Finsupp.single d c) F = c • liftP W M p d F :=
  Finsupp.sum_single_index (zero_smul _ _)

theorem liftT_add (p : Path T X Y) (τ τ' : TotT G p) (F : Fn G X) :
    liftT W M p (τ + τ') F = liftT W M p τ F + liftT W M p τ' F :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

def rowDatum (ρ : G.RealVec) (Φ : G.Datum) : PureT G (rowPath T 0 D.R.m) := rowFam 0 D.R.m (W.datum ρ Φ)

def thetaChi (ρ : G.RealVec) (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) : Fn G (.grid D.R.m 0) :=
  liftP W M (rowPath T 0 D.R.m) (rowDatum W ρ Φ) u

def ThetaConv (ρ : G.RealVec) (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) : Prop :=
  PathConv W M (rowPath T 0 D.R.m) (rowDatum W ρ Φ) u

def stabilizerEmbedding {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : GA D A) : GA D B :=
  (GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom h).choose

theorem embRel_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : GA D A) (g : GA D B) :
    EmbRel B A d.ι g h ↔ g = stabilizerEmbedding d h :=
  have H := (GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom h).choose_spec
  ⟨H.2 g, fun e => e ▸ H.1⟩

variable (G) in

def embTop : GA D (G.V (.top 0)) → GA D (G.V (.grid D.R.m 0)) :=
  stabilizerEmbedding (G.rowDec 0 (by have := D.R.two_le_m; omega))

def besInt (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) (h : GA D (G.V (.top 0)))
    (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) : ℂ :=
  φ h * F ((n : GA D _) * embTop G h) * star (besChar W.ψ G.besTop (n : GA D _))

def Bplus (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) : ℂ :=
  ∫ h in M.fd (.top 0), ∫ n in M.fdN, besInt W φ F h n ∂M.νN ∂M.ν (.top 0)

def BplusConv (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) : Prop :=
  (∀ h, IntegrableOn (besInt W φ F h) M.fdN M.νN) ∧
    IntegrableOn (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0))

theorem besInt_eq (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    besInt W φ F = GlobalTheory.Per.besFun W.ψ G.besTop (embTop G) (star φ) F := by
  funext h n
  have e : (G.besTop.y : GA D (G.V (.grid D.R.m 0))) = 1 := rfl
  rw [besInt, GlobalTheory.Per.besFun, e, mul_one, Pi.star_apply, star_star]

theorem Bplus_eq (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) : Bplus W M φ F =
    GlobalTheory.Per.besPer W.ψ G.besTop (M.ν (.top 0)) (M.fd (.top 0)) M.νN M.fdN (embTop G) (star φ) F := by
  rw [Bplus, besInt_eq]; rfl

theorem Bplus_smul (c c' : ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus W M (c • φ) (c' • F) = c * c' * Bplus W M φ F := by
  have e : ∀ h n, besInt W (c • φ) (c' • F) h n = c * c' * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]

theorem Bplus_of_equivariant (hM : M.νN M.fdN = 1) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0))
    (hψ : ∀ n ∈ NFlag _ G.besTop.e, ‖besChar W.ψ G.besTop n‖ = 1)
    (hF : ∀ n ∈ NFlag _ G.besTop.e, ∀ g, F (n * g) = besChar W.ψ G.besTop n * F g) :
    Bplus W M φ F = ∫ h in M.fd (.top 0), φ h * F (embTop G h) ∂M.ν (.top 0) := by
  have e : ∀ h n, besInt W φ F h n = φ h * F (embTop G h) := fun h n => by
    have h1 := Complex.mul_conj' (besChar W.ψ G.besTop (n : GA D _))
    rw [hψ _ n.2] at h1
    rw [besInt, hF _ n.2]
    linear_combination (norm := (simp; ring_nf)) φ h * F (embTop G h) * h1
  simp [Bplus, e, Measure.real, hM]

def pairVec {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) : (Bridge.Gf V → c.W) →ₗ[ℂ] (GA D V → ℂ) :=
  ξ.compLeft _ ∘ₗ c.ext

theorem pairVec_apply {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) (h : GA D V) :
    pairVec c ξ Ψ h = ξ (c.ρ h⁻¹ (Ψ ((finHom V).rangeRestrict h))) := rfl

def fPsiPhi (ρ : G.RealVec) {c : CoefA (G.V (.top 0))} (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf (G.V (.top 0)) → c.W)
    (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) : ℂ :=
  Bplus W M (pairVec c ξ Ψ) (thetaChi W M ρ Φ u)

def FConv (ρ : G.RealVec) {c : CoefA (G.V (.top 0))} (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf (G.V (.top 0)) → c.W)
    (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) : Prop :=
  ThetaConv W M ρ Φ u ∧ BplusConv W M (pairVec c ξ Ψ) (thetaChi W M ρ Φ u)

theorem fPsiPhi_smul (ρ : G.RealVec) {c : CoefA (G.V (.top 0))} (ξ : Module.Dual ℂ c.W) (a b : ℂ)
    (Ψ : Bridge.Gf (G.V (.top 0)) → c.W) (Φ : G.Datum) (u : GA D (Yc D 0) → ℂ) :
    fPsiPhi W M ρ ξ (a • Ψ) Φ (b • u) = a * b * fPsiPhi W M ρ ξ Ψ Φ u := by
  have e : thetaChi W M ρ Φ (b • u) = b • thetaChi W M ρ Φ u := pathLift_smul W M (X := .grid 0 0) b u _ _
  rw [fPsiPhi, map_smul, e, Bplus_smul]; rfl

theorem fPsiPhi_add {ρ : G.RealVec} {c : CoefA (G.V (.top 0))} {ξ : Module.Dual ℂ c.W}
    {Ψ : Bridge.Gf (G.V (.top 0)) → c.W} {Φ : G.Datum} {u u' : GA D (Yc D 0) → ℂ}
    (h : FConv W M ρ ξ Ψ Φ u) (h' : FConv W M ρ ξ Ψ Φ u') :
    fPsiPhi W M ρ ξ Ψ Φ (u + u') = fPsiPhi W M ρ ξ Ψ Φ u + fPsiPhi W M ρ ξ Ψ Φ u' := by
  have e : thetaChi W M ρ Φ (u + u') = thetaChi W M ρ Φ u + thetaChi W M ρ Φ u' :=
    pathLift_add W M (X := .grid 0 0) _ _ h.1 h'.1
  have e2 : ∀ φ F F' x n, besInt W φ (F + F') x n = besInt W φ F x n + besInt W φ F' x n := fun φ F F' x n => by
    simp only [besInt, Pi.add_apply]; ring
  rw [fPsiPhi, e, fPsiPhi, fPsiPhi, Bplus, Bplus, Bplus, ← integral_add h.2.2 h'.2.2]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [e2]
  exact integral_add (h.2.1 x) (h'.2.1 x)

example (t : T) : (givenPath t 2).arrows = [.down t 0 1, .down t 0 0, .right 0 0, .right 1 0] ∧
    (oppPath t 2).arrows = [.right 0 2, .right 1 2, .down t 2 1, .down t 2 0] := ⟨rfl, rfl⟩

example (f : ∀ i : Fin 2, Sch G (.right i 0)) (u : Fn G (.grid 0 0)) :
    liftP W M (rowPath T 0 2) (rowFam 0 2 f) u = liftA W M (.right 1 0) (f 1) (liftA W M (.right 0 0) (f 0) u) := rfl

end GlobalTheory.FunObj

end
