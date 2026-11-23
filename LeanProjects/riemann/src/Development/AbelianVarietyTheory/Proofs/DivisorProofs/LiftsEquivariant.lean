import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum

noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def HeckeNormal {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Subgroup (GA D V)) (H : HMod (MMap M))
    {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) : Prop :=
  ∃ T : ok × ℕ → Module.End ℂ H.H, (∀ P, T (P, 0) = 1) ∧
    (∀ (P : ok) (k : ℕ), k ≤ V.rank → ∀ α : GA D V, IsHeckeAt V (pl P) k α → ∀ B : Finset (GA D V),
      Bridge.IsDC J α⁻¹ B → ∀ x, H.e (T (P, k) x) = heckeOn M B (H.e x)) ∧
    Col.PairComm T ∧ ∀ i, Commute (T i) (LinearMap.adjoint (T i))

def IsDefEig (V : HSp D) (J : Subgroup (Bridge.Gf V)) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (g : ok → ℂ[X]) (f : Bridge.Gf V → W) : Prop :=
  ∀ i : ok × ℕ, 1 ≤ i.2 → i.2 ≤ V.rank → ∀ x : Bridge.Gf V, isTEnv V pl ok i x → ∀ B : Finset (Bridge.Gf V),
    (∀ a ∈ B, isLocEnv V pl ok i a) → Bridge.IsDC J x B → Bridge.dcOp B f = eigOf (q i.1) (g i.1) i.2 • f

open Classical in

def polOf {Pl0 : Type} (ok : Set Pl0) (r : ℕ) (q : Pl0 → ℕ) (c : ok × ℕ → ℂ) (P : Pl0) : ℂ[X] :=
  if h : P ∈ ok then Col.heckePoly r (fun P : ok => q P) c ⟨P, h⟩ else 1

theorem polOf_apply {Pl0 : Type} (ok : Set Pl0) (r : ℕ) (q : Pl0 → ℕ) (c : ok × ℕ → ℂ) (P : ok) :
    polOf ok r q c P = Col.heckePoly r (fun P : ok => q P) c P := dif_pos P.2

theorem mem_hPart {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Subgroup (GA D V)} {H : HMod (MMap M)}
    {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} (hq : ∀ P : ok, 0 < q P)
    {T : ok × ℕ → Module.End ℂ H.H}
    (hT : ∀ (P : ok) (k : ℕ), k ≤ V.rank → ∀ α : GA D V, IsHeckeAt V (pl P) k α → ∀ B : Finset (GA D V),
      Bridge.IsDC J α⁻¹ B → ∀ x, H.e (T (P, k) x) = heckeOn M B (H.e x))
    {c : ok × ℕ → ℂ} {e : H.H} (he : ∀ i, T i e = c i • e) :
    H.e e ∈ hPart M J ok pl q (polOf ok V.rank q c) := by
  simp only [hPart, Submodule.mem_iInf, LinearMap.mem_ker]
  intro P hP k hk α hα B hB
  have h1 := eigOf_heckePolyOf (hq ⟨P, hP⟩) (fun k => c (⟨P, hP⟩, k)) hk
  have h2 : polOf ok V.rank q c P = _ := polOf_apply ok V.rank q c ⟨P, hP⟩
  rw [LinearMap.sub_apply, ← hT ⟨P, hP⟩ k hk α hα B hB, he, map_smul, LinearMap.smul_apply, LinearMap.id_apply, h2,
    sub_eq_zero]
  exact congrArg (· • H.e e) h1.symm

theorem side_le {G Pl0 : Type} [Group G] [Fintype G] {V Y : HSp D} {c : CoefA V} {β : GL (Fin V.rank) (EAf D)}
    {L : LevDat D.host.E ℂ V.rank} {pl : Pl0 → Pl D.host.E} {ok : Set Pl0} {S : CSD D.what₂.LL}
    {act : Representation D.what₂.LL G S.Forms} {op : ok × ℕ → Module.End D.what₂.LL S.Forms}
    (B : Bridge.SideReal D V (Bridge.envOf c.coef (levEnvOf V β L pl ok)) S act op fun i => i.2)
    (N : HMod (Bridge.Gf V → c.W))
    (hN : N.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J B.pres.y))
    {j : S.Forms →ₛₗ[D.what₂.embLL] N.H} (hj : ∀ x, N.e (j x) = B.pres.extL x)
    (hc : Col.PairComm op) (hs : Col.SplitOver op) {q : Pl0 → ℕ} (hq : ∀ P : ok, 0 < q P) {t n : ℕ}
    {bl : List (ok → D.what₂.LL)} (hV : V.rank = n) (hn : n = Y.rank + bl.length * t)
    (hdeg : ∀ P, op (P, 0) = 1 ∧ ∀ k, V.rank < k → op (P, k) = 0)
    {SY : D.what₂.Tau → SPar} {M : DSModel Y SY} {J : Subgroup (GA D Y)} {H : HMod (MMap M)}
    (hT : HeckeNormal M J H ok pl) (Θ : N.H →ₗ[ℂ] H.H) (s : ok → ℂ)
    (hup : ∀ f : Pl0 → ℂ[X], (∀ P ∈ ok, (f P).natDegree ≤ Y.rank) → ∀ e : H.H, H.e e ∈ hPart M J ok pl q f →
      IsDefEig V (levEnv V β L).J ok pl q (fun P => (f P).comp (C (s P) * X) *
        ((bl.map fun ν => Col.blockPoly (ν P) (q P) t).prod).map D.what₂.embLL) (N.e (LinearMap.adjoint Θ e))) :
    (LinearMap.range (LinearMap.adjoint Θ)).comap j ≤ Col.blockSum n (fun P : ok => q P) t bl op := by
  subst hV
  have hf := model_form (W := c.W) (ι := Bridge.ratF V) (ρ := c.coef.ρ) (J := (levEnv V β L).J) (χ := (levEnv V β L).χ)
    B.pres N hN hj
  obtain ⟨T, hT0, hTt, hTc, hTn⟩ := hT
  refine comap_range_adjoint_le_blockSum (r := Y.rank) (q := fun P : ok => q P) hf.1 hf.2.1 hc hs hq hn
    (fun P => (hdeg P).1) (fun P => (hdeg P).2) Θ hT0 hTc hTn s ?_
  intro x e he P k hk1 hk U hU
  have h0 : ∀ P ∈ ok, (polOf ok Y.rank q x P).natDegree ≤ Y.rank := fun P hP => by
    have h : polOf ok Y.rank q x P = _ := polOf_apply ok Y.rank q x ⟨P, hP⟩
    rw [h]
    exact natDegree_heckePolyOf _ _ _
  have h3 := hup (polOf ok Y.rank q x) h0 e (mem_hPart hq hTt he) (P, k) hk1 hk _ (B.hecke.hx_ok (P, k) ⟨hk1, hk⟩) _
    (B.hecke.hA_loc (P, k) ⟨hk1, hk⟩) (B.hecke.hDC (P, k) ⟨hk1, hk⟩)
  have h4 := (model_dcOp (W := c.W) (ι := Bridge.ratF V) (ρ := c.coef.ρ) (J := (levEnv V β L).J) (χ := (levEnv V β L).χ)
    B.pres N hN hj (B.hecke.op_eq (P, k) ⟨hk1, hk⟩) hU _).trans h3
  simp only [polOf_apply] at h4
  have hinj : Function.Injective N.e := hN.1
  exact hinj (h4.trans (N.e.map_smul _ _).symm)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def HeckeOps : Prop :=
  (∀ t, HeckeNormal (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) R.HE (A.ok t) R.pl) ∧
    ∀ i t, HeckeNormal (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (R.HW i (sg0 D A)) (A.ok t) R.pl

def HeckeUpRows : Prop :=
  ∀ (t : T) (f : Pl0 → ℂ[X]), (∀ P ∈ A.ok t, (f P).natDegree ≤ (Yc D 0).rank) → ∀ e : R.HE.H,
    R.HE.e e ∈ hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok t) R.pl A.q f →
      IsDefEig D.sp.X' (levEnv _ R.βX (R.datXt t)).J (A.ok t) R.pl A.q
        (fun P => (f P).comp (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) * ((A.fam.R t).blockProd P).map D.what₂.embLL)
        ((R.HX t).e (LinearMap.adjoint (R.Th t) e))

def HeckeUpLifts : Prop :=
  ∀ (i : Fin D.R.m) (t : T) (f : Pl0 → ℂ[X]), (∀ P ∈ A.ok t, (f P).natDegree ≤ (Wc D i).rank) →
    ∀ w : (R.HW i (sg0 D A)).H,
    (R.HW i (sg0 D A)).e w ∈ hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok t) R.pl A.q f →
      IsDefEig (Vc D i) (levEnv _ (R.βV i) (R.datVt i t)).J (A.ok t) R.pl A.q
        (fun P => (f P).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) *
          ((A.fam.L i t).blockProd P).map D.what₂.embLL)
        ((R.HV i t).e (LinearMap.adjoint (R.thG i t) w))

def LiftsEquivariant : Prop :=
  (∀ t g (v : (A.MtildeCSD t).Forms), R.Th t (R.jX t (A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) ∧
    ∀ i t g (v : (A.MtCSD i t).Forms),
      R.thG i t (R.jV i t (A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t v))

theorem postOn_gaL {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (β : GL (Fin V.rank) (EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (x : MMap M) :
    postOn M (gaL V β L eG c) x = ∑ g, c g • postOn M (actL V β L (eG g)) x := by
  ext v h
  simp [postOn, gaL, LinearMap.sum_apply, Finset.sum_apply]

variable {R} {F : Face D A}

theorem proj_rows (hC : R.Char F) (y : R.HE.H) : ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  refine hC.models.HE.1 ?_
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  refine Eq.trans ?_ ((postOn_gaL (R.MY 0) (R.βY 0) (R.dat0 R.triv) R.eG _ _).symm.trans (sub_eq_zero.1 h2))
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gE]; rfl

theorem proj_lifts {s : ℕ} (hC : R.Char F) (hOk : A.fam.Ok s) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g (R.thG i t y) = R.thG i t y := by
  have h1 : R.thF i t y ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    (hC.models.HW i (sg0 D A)).2.1.ge (hC.thP.thF_mem i t y)
  obtain ⟨z, hz⟩ := h1
  have hs : ∀ a, sg0 D A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have h2 : R.thG i t y = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g z := by
    refine (hC.models.HW i _).1 ?_
    rw [hC.thP.thG, ← hz, map_sum]
    refine (postOn_gaL (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG _ _).trans ?_
    exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gW, RealDat.eC, hs]; rfl
  rw [h2]
  exact idem_idem _ hOk.irr _ z

theorem r_eq (hC : R.Char F) : A.r = D.R.r := hC.fam.tie.choose_spec.choose_spec.choose_spec.ranks.2.1

theorem rows_le {s : ℕ} (hC : R.Char F) (hOk : A.fam.Ok s) (hT : HeckeOps R) (hR : HeckeUpRows R)
    (hG : LiftsEquivariant R) (t : T) :
    (LinearMap.range (LinearMap.adjoint (R.Th t))).comap (R.jX t) ≤ (A.fam.R t).ZHg A.X := by
  have hrk : (Yc D 0).rank = A.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), r_eq hC]
    simp [Ranks.rankY]
  have hn : (A.fam.R t).n = (Yc D 0).rank + (A.fam.R t).bl.length * (A.fam.R t).t := by
    rw [hrk]
    exact congrArg (fun k => A.r + k * A.t) List.length_ofFn.symm
  exact le_inf
    (side_le (R.B.R t) (R.HX t) (hC.models.HX t) (hC.models.jX t) (hOk.what₂ t).comm (hOk.what₂ t).split (q := A.q)
      (hOk.what₂ t).q_pos R.B.rankR hn (hC.fam.degR t) (hT.1 t) (R.Th t) _ (hR t))
    (model_good (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ) (J := (levEnv _ R.βX (R.datXt t)).J)
      (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t) (hC.models.jX t) (hOk.what₂ t).act hOk.irr R.gE (hG.1 t)
      fun y => proj_rows hC _)

theorem lifts_le {s : ℕ} (hC : R.Char F) (hOk : A.fam.Ok s) (hT : HeckeOps R) (hL : HeckeUpLifts R)
    (hG : LiftsEquivariant R) (i : Fin D.R.m) (t : T) :
    (LinearMap.range (LinearMap.adjoint (R.thG i t))).comap (R.jV i t) ≤ (A.fam.L i t).ZHg A.X := by
  have hrk : (Wc D i).rank = A.r := by
    rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2, r_eq hC]
  have hn : (A.fam.L i t).n = (Wc D i).rank + (A.fam.L i t).bl.length * (A.fam.L i t).t := by
    rw [hrk]
    show A.r + A.t = A.r + 1 * A.t
    rw [one_mul]
  exact le_inf
    (side_le (R.B.L i t) (R.HV i t) (hC.models.HV i t) (hC.models.jV i t) (hOk.lifts i t).comm (hOk.lifts i t).split
      (q := A.q) (hOk.lifts i t).q_pos (R.B.rankL i) hn (hC.fam.degL i t) (hT.2 i t) (R.thG i t) _ (hL i t))
    (model_good (W := (R.cV i).W) (ι := Bridge.ratF (Vc D i)) (ρ := (R.cV i).coef.ρ)
      (J := (levEnv _ (R.βV i) (R.datVt i t)).J) (χ := (levEnv _ (R.βV i) (R.datVt i t)).χ) (R.B.L i t).pres (R.HV i t) (hC.models.HV i t) (hC.models.jV i t) (hOk.lifts i t).act hOk.irr
      (R.gW i (sg0 D A)) (hG.2 i t) fun y => proj_lifts hC hOk i t y)

theorem lBlock {s : ℕ} (hC : R.Char F) (hOk : A.fam.Ok s) (hT : HeckeOps R) (hR : HeckeUpRows R) (hL : HeckeUpLifts R)
    (hG : LiftsEquivariant R) : R.LBlock F :=
  ⟨fun t x hx => rows_le hC hOk hT hR hG t ((mem_range_adjoint_tw (twAt D.what₂.embLL A.v0) (R.Th t) (R.jX t x)).1 hx),
    fun i t x hx => lifts_le hC hOk hT hL hG i t
      ((mem_range_adjoint_tw (twAt D.what₂.embLL A.v0) (R.thG i t) (R.jV i t x)).1 hx)⟩

end Record

end GlobalTheory.AdjBlock

end
