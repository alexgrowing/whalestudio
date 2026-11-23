import Formalism.SharpRestriction.GrowthBounds.ChartComparison.StepIn
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ExistsPrimeToLe
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsIdealDenominator

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Idx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau]

theorem FiC_comp (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (lam : Tau → DomWeight n) {c c' : Type}
    (yc : c → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (r : c' → c) (hr : Function.Surjective r)
    (ψ : c → Frames (gramC J emb) → ℂ) :
    (fun a => ψ (r a)) ∈ FiC S emb lam (fun a => yc (r a)) ↔ ψ ∈ FiC S emb lam yc := by
  unfold FiC
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, ?_⟩
    funext a
    obtain ⟨a', rfl⟩ := hr a
    exact congrFun h a'
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, ?_⟩
    funext a
    exact congrFun h (r a)

end Idx

variable {D : D7} {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}

def IntAtI (V : ValTied u eV i hi K) (w : D.what₂.places.Pl) (x : ((D.fm u).lat i).V) (c : (D.mem u).C.cls i) : Prop :=
  ∀ B : GL (Fin (D.R.N i)) D.host.E,
    IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)) B →
    ∃ P ∈ IntSpan D w ((D.fm u).lam i),
      ∀ z, (D.fm u).emb i x c z =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) P (V.eY z)

theorem locW_intAtI (V : ValTied u eV i hi K) (w : D.what₂.places.Pl) (x : ((D.fm u).lat i).V)
    (hx : x ∈ Formalism.BasicNotions.locW D.what₂.places w ((D.fm u).lat i).L) (c : (D.mem u).C.cls i) : IntAtI V w x c := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    intro B hB
    exact (V.lat y).1 hy w c B hB
  | zero =>
    intro B _
    refine ⟨0, AddSubgroup.zero_mem _, fun z => ?_⟩
    rw [map_zero, map_zero]
    rfl
  | add y z _ _ h1 h2 =>
    intro B hB
    obtain ⟨P, hP, hPy⟩ := h1 B hB
    obtain ⟨Q, hQ, hQz⟩ := h2 B hB
    refine ⟨P + Q, AddSubgroup.add_mem _ hP hQ, fun t => ?_⟩
    rw [map_add, map_add]
    show (D.fm u).emb i y c t + (D.fm u).emb i z c t = _
    rw [hPy t, hQz t]
    rfl
  | smul a y _ h1 =>
    intro B hB
    obtain ⟨P, hP, hPy⟩ := h1 B hB
    refine ⟨D.what₂.embLL a.1 • P, intSpan_smul w _ a.1 a.2 hP, fun t => ?_⟩
    rw [Subring.smul_def, LinearMap.map_smulₛₗ, map_smul]
    show D.what₂.embLL a.1 * (D.fm u).emb i y c t = _
    rw [hPy t]
    rfl

theorem exists_denI (u : D.what₂.Word) (i : ℕ) (x : ((D.fm u).lat i).V) :
    ∃ d : 𝓞 D.what₂.LL, d ≠ 0 ∧ d • x ∈ ((D.fm u).lat i).L :=
  _root_.UpperTheory.Reformulated.B.ExistsIdealDenominator.exists_denI u i x

theorem locWBackI (V : ValTied u eV i hi K) (w : D.what₂.places.Pl) (x : ((D.fm u).lat i).V) (hx : ∀ c, IntAtI V w x c) :
    x ∈ Formalism.BasicNotions.locW D.what₂.places w ((D.fm u).lat i).L := by
  have key : ∀ (r : 𝓞 D.what₂.LL) (v : ((D.fm u).lat i).V), r • v = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) • v :=
    fun r v => (algebraMap_smul D.what₂.LL r v).symm
  obtain ⟨d, hd0, hdL⟩ := exists_denI u i x
  obtain ⟨s, hsP, hsv⟩ := exists_prime_to_le (D.plEq w) d hd0
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ Submodule.zero_mem _)
  have hsL : s • x ∈ ((D.fm u).lat i).L := by
    refine (V.lat (s • x)).2 ?_
    intro w' c B hB
    by_cases hw : w' = w
    · subst hw
      have hsint : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ∈ Formalism.BasicNotions.intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [Formalism.L2.G.val_nonneg_iff, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (D.plEq w').intValuation_le_one s
      obtain ⟨P, hP, hPx⟩ := hx c B hB
      refine ⟨D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) • P, intSpan_smul w' _ _ hsint hP, fun t => ?_⟩
      rw [key, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]
    · have hne : D.plEq w' ≠ D.plEq w := fun h => hw (D.plEq.injective h)
      have hdne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL d ≠ 0 := by
        simpa using hd0
      set q : D.what₂.LL := algebraMap (𝓞 D.what₂.LL) D.what₂.LL s / algebraMap (𝓞 D.what₂.LL) D.what₂.LL d with hq
      have hqint : q ∈ Formalism.BasicNotions.intW D.what₂.places w' := by
        show (0 : WithTop ℤ) ≤ D.what₂.places.val w' _
        rw [Formalism.L2.G.val_nonneg_iff, hq, map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        have hdv : (D.plEq w').intValuation d ≠ 0 := (D.plEq w').intValuation_ne_zero d hd0
        rw [div_le_one₀ (zero_lt_iff.2 hdv)]
        exact hsv _ hne
      have hsx : s • x = q • (d • x) := by
        rw [key, key, smul_smul, hq, div_mul_cancel₀ _ hdne]
      obtain ⟨P, hP, hPx⟩ := (V.lat (d • x)).1 hdL w' c B hB
      refine ⟨D.what₂.embLL q • P, intSpan_smul w' _ q hqint hP, fun t => ?_⟩
      rw [hsx, LinearMap.map_smulₛₗ, LinearMap.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hPx t]
  have hsu : (D.plEq w).intValuation s = 1 := by
    apply le_antisymm ((D.plEq w).intValuation_le_one s)
    by_contra hlt
    exact hsP (((D.plEq w).intValuation_lt_one_iff_mem s).1 (lt_of_not_ge hlt))
  have hsne : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by simpa using hs0
  have htint : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ Formalism.BasicNotions.intW D.what₂.places w := by
    show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
    rw [Formalism.L2.G.val_nonneg_iff, map_inv₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hsu, inv_one]
  have hx' : x = (⟨_, htint⟩ : Formalism.BasicNotions.intW D.what₂.places w) • (s • x) := by
    rw [Subring.smul_def, key, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsL)

theorem locWCritI (V : ValTied u eV i hi K) (w : D.what₂.places.Pl) (x : ((D.fm u).lat i).V) :
    x ∈ Formalism.BasicNotions.locW D.what₂.places w ((D.fm u).lat i).L ↔ ∀ c, IntAtI V w x c :=
  ⟨fun hx c => locW_intAtI V w x hx c, locWBackI V w x⟩

def chU (u : D.what₂.Word) (i : ℕ) : (D.mem u).C.cls i → Unit := fun _ => ()

def oneChart (K : ClsTied u i hi) (β : Unit) :
    LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chU u i c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1) where
  lev := K.lev
  y := fun c => K.y c.1
  y_bij := ⟨fun a b h => Subtype.ext (K.y_bij.1 h), fun q => by
    obtain ⟨c, hc⟩ := K.y_bij.2 q
    exact ⟨⟨c, Subsingleton.elim _ _⟩, hc⟩⟩
  y_lat := fun c => K.y_lat c.1
  stabI := fun c => K.stabI c.1
  stabI_inj := fun c => K.stabI_inj c.1
  stabI_range := fun c => K.stabI_range c.1

theorem oneChart_lev (K : ClsTied u i hi) (β : Unit) : (oneChart K β).lev = K.lev := rfl

set_option maxHeartbeats 2000000 in

theorem valTied_toG (V : ValTied u eV i hi K) :
    ValuationCompatibleChart (D.fm u) V.eY (fun _ => True) (chU u i) (lat := clsCrd D u i hi) (oneChart K) where
  Fi := fun φ => by
    rw [V.Fi φ]
    constructor
    · intro h β
      exact (FiC_comp K.lev (embT D) (lamT u i) K.y (fun c : {c // chU u i c = β} => c.1)
        (fun c => ⟨⟨c, Subsingleton.elim _ _⟩, rfl⟩) (fun c z => φ c (V.eY.symm z))).2 h
    · intro h
      exact (FiC_comp K.lev (embT D) (lamT u i) K.y (fun c : {c // chU u i c = ()} => c.1)
        (fun c => ⟨⟨c, Subsingleton.elim _ _⟩, rfl⟩) (fun c z => φ c (V.eY.symm z))).1 (h ())
  rat := fun φ => V.rat φ
  lat := fun w _ x => locWCritI V w x

variable {p : ℕ}

set_option maxHeartbeats 2000000 in

def stepInOne (V : ValTied u eV i hi K) (G : GAtP p) (dt : DetTie K.lev) (cmpt : Unit → Type) [∀ β, Fintype (cmpt β)]
    (eC : (Σ β, cmpt β) ≃ G.comp) (loc : ∀ β, LocAt D.host.F D.host.E (D.R.N i) (gatCh G fun a : cmpt β => eC ⟨β, a⟩))
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau) : StepIn (D.fm u) i hi G where
  T := (D.mem u).A.T
  bad := badG D
  eY := V.eY
  okW := fun _ => True
  Ch := Unit
  chOf := chU u i
  lat := clsCrd D u i hi
  K := oneChart K
  val := valTied_toG V
  tw := fun _ => DetTw.ofChiD dt (cTw D i)
  cmpt := cmpt
  eC := eC
  loc := loc
  pos := pos

variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 2000000 in

def stepInMid (F : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (G : GAtP p)
    (dt : ∀ β, DetTie (F.ch i h1 h2 β).lev) (cmpt : Ch i → Type) [∀ β, Fintype (cmpt β)]
    (eC : (Σ β, cmpt β) ≃ G.comp) (loc : ∀ β, LocAt D.host.F D.host.E (D.R.N i) (gatCh G fun a : cmpt β => eC ⟨β, a⟩))
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau) : StepIn (D.fm u) i (le_of_succ_m h2) G where
  T := (D.mem u).A.T
  bad := badG D
  eY := F.eYC i h1 h2
  okW := fun _ => True
  Ch := Ch i
  chOf := chOf i
  lat := fun c => clsCrd D u i (le_of_succ_m h2) c
  K := F.ch i h1 h2
  val := F.valC i h1 h2
  tw := fun β => DetTw.ofChiD (dt β) (cTw D i)
  cmpt := cmpt
  eC := eC
  loc := loc
  pos := pos

def stepInTop (F : FormsTiedSym D u Ch chOf) (G : GAtP p) (dt : DetTie (F.cls D.R.m le_rfl (Or.inr rfl)).lev)
    (cmpt : Unit → Type) [∀ β, Fintype (cmpt β)] (eC : (Σ β, cmpt β) ≃ G.comp)
    (loc : ∀ β, LocAt D.host.F D.host.E (D.R.N D.R.m) (gatCh G fun a : cmpt β => eC ⟨β, a⟩))
    (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ D.what₂.Tau) : StepIn (D.fm u) D.R.m le_rfl G :=
  stepInOne (F.val D.R.m le_rfl (Or.inr rfl)) G dt cmpt eC loc pos

end Formalism.MainNotions.G.CmpJ

end
