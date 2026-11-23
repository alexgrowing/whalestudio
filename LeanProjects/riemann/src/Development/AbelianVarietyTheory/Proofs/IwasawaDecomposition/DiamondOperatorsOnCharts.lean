import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetFramesInvariantRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRowStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaChart

theorem normal_rep {G D A : Type} [Group G] [MulAction G D] (f : D → A) (pref : D → Prop)
    (h : ∀ q, pref q ↔ f q = Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩))
    (d d' : D) (hd : ∀ g : G, f (g • d') = f (g • d)) :
    f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) d')) = f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) d)) := by
  have h1 : ∀ (q : D) (g₀ : G), (fun r => ∃ g : G, r = f (g • g₀ • q)) = fun r => ∃ g : G, r = f (g • q) := fun q g₀ => by
    funext r
    refine propext ⟨fun ⟨g, e⟩ => ⟨g * g₀, by rw [mul_smul]; exact e⟩, fun ⟨g, e⟩ => ⟨g * g₀⁻¹, by
      rw [mul_smul, inv_smul_smul]; exact e⟩⟩
  have h2 : ∀ q : D, f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) q)) =
      Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩) := fun q => by
    have hex : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = Quotient.mk (MulAction.orbitRel G D) q ∧ pref p := by
      obtain ⟨g, hg⟩ := Classical.epsilon_spec (p := fun r => ∃ g : G, r = f (g • q)) ⟨f q, 1, by rw [one_smul]⟩
      refine ⟨g • q, Quotient.sound ⟨g, rfl⟩, (h _).2 ?_⟩
      rw [h1]
      exact hg.symm
    unfold prefRep
    rw [dif_pos hex]
    obtain ⟨g, hg⟩ : ∃ g : G, g • q = hex.choose := Quotient.exact hex.choose_spec.1
    have h3 := (h _).1 hex.choose_spec.2
    rw [h3, ← hg, h1]
  rw [h2, h2]
  simp only [hd]

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem mv_dia (q : PtAt R sel mu cst u j) (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    PtY.mv q (DecoSet.dia1 P a q.1.1.deco) = ⟨(⟨(DecoSet.dia1 P a q.1.1.deco, q.1.1.1.2), q.1.1.2⟩, q.1.2), q.2⟩ := by
  unfold PtY.mv
  exact dif_pos ⟨q.1.1.2, q.2⟩

theorem cosetIn_dia (q : PtAt R sel mu cst u j) (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    cosetIn (PtY.mv q (DecoSet.dia1 P a q.1.1.deco) : PtAt R sel mu cst u j) = cosetIn q := by
  rw [mv_dia]
  rfl

theorem cosetIn_of_ne (h : j + 1 ≠ R.m) (q : PtAt R sel mu cst u j) : cosetIn q = fun _ => ∅ := by
  have h2 : q.1.2 = ∅ := by
    have := q.2
    rw [ysAt_ys_of_ne sel mu cst h] at this
    exact this
  funext P
  unfold cosetIn
  rw [h2]
  simp

end Pt

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev dp (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl) :
    (I.stp u a i).D c.1 := PtY.mv ((I.stp u a i).rep c) (DecoSet.dia1 P s ((I.stp u a i).rep c).1.1.deco)

theorem cosetIn_rep (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ)
    (c : (I.stp u a i).Cl) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c))) = cosetIn ((I.stp u a i).rep c) := by
  by_cases h : i + 1 = B.R.m
  · have h2 := @normal_rep ((I.stp0 u a i).G c.1) ((I.stp0 u a i).D c.1) _ _ ((I.stp0 u a i).actD c.1) (fun q => cosetIn q) (I.pref u a i c.1)
      (fun q => ⟨fun hq => hq.2.1 h, fun hq => ⟨fun h0 => by have := B.R.two_le_m; omega, fun _ => hq, fun h0 => by omega⟩⟩)
      ((I.stp u a i).rep c) (dp I u a i P s c) (fun g => by
        have e := ((l.lev u a).lev i).dia_act c.1 P s g ((I.stp u a i).rep c)
        exact (congrArg (fun q : (I.stp0 u a i).D c.1 => cosetIn q) e.symm).trans (cosetIn_dia _ P s))
    refine h2.trans ?_
    exact congrArg (fun q => cosetIn ((I.stp u a i).rp c.1 q)) ((I.stp u a i).rp_spec c.1 c.2)
  · rw [cosetIn_of_ne h, cosetIn_of_ne h]

set_option maxHeartbeats 1000000 in

theorem exists_level (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : Ch → GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl)
    (δ : GA B (B.R.N i)) (hδ : PtOf (y c * δ * k (chOf c)) (dp I u a i P s c).1.1) (β : Ch)
    (hβ : chOf ((I.stp u a i).cl c.1 (dp I u a i P s c)) = β) :
    ∃ x : U β, y c * δ = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u a i).gam c.1 ((I.stp u a i).mv c.1 (dp I u a i P s c))) * y ((I.stp u a i).cl c.1 (dp I u a i P s c)) * x.1 ∧
      ((chi β x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 ((I.stp u a i).mv c.1 (dp I u a i P s c)) : B.LLˣ) : B.LL) := by
  subst hβ
  have hch : chOf ((I.stp u a i).cl c.1 (dp I u a i P s c)) = chOf c := (h.key _ _).2 ⟨rfl, cosetIn_rep I l u a i P s c⟩
  have hg := (I.stp u a i).mv_smul c.1 (dp I u a i P s c)
  have hco := cosetIn_rep I l u a i P s c
  have hco' : cosetIn (dp I u a i P s c) = cosetIn ((I.stp u a i).rep c) := cosetIn_dia _ P s
  generalize (I.stp u a i).mv c.1 (dp I u a i P s c) = g at hg ⊢
  rw [← hch] at hδ
  have hlev := h.lev ((I.stp u a i).cl c.1 (dp I u a i P s c))
  have hchr := h.chr ((I.stp u a i).cl c.1 (dp I u a i P s c))
  generalize y ((I.stp u a i).cl c.1 (dp I u a i P s c)) = y' at hlev hchr ⊢
  obtain ⟨γ, κ⟩ := g
  have hk : (I.stp u a i).act c.1 (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c))) =
      (I.stp u a i).act c.1 (γ⁻¹, 1) (dp I u a i P s c) := by
    refine Eq.trans ?_ (congrArg ((I.stp u a i).act c.1 (γ⁻¹, 1)) hg)
    refine Eq.trans ?_ (((I.stp u a i).actD c.1).mul_smul (γ⁻¹, 1) (γ, κ) _)
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul]
    rfl
  have hpt : PtOf (y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * (y c * δ))) * k (chOf ((I.stp u a i).cl c.1 (dp I u a i P s c))))
      ((I.stp u a i).act c.1 (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c)))).1.1 := by
    rw [hk, mul_inv_cancel_left, mul_assoc]
    exact GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ _ _ _ _ _ γ⁻¹ _ _ hδ
  have hx := (hlev _ _ hpt).2 ⟨(1, κ), map_one (ufGL _ _), rfl, by
    refine Eq.trans ?_ (hco'.trans hco.symm)
    refine (congrArg (fun q : (I.stp u a i).D c.1 => cosetIn q) hk).trans ?_
    exact GlobalTheory.T.couplingCoset_frames_invariant_rational_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ⁻¹ rfl rfl⟩
  refine ⟨⟨_, hx⟩, ?_, hchr ⟨_, hx⟩ (1, κ) (map_one (ufGL _ _)) hpt⟩
  show y c * δ = ratAd B.host.F γ * y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * (y c * δ)))
  rw [mul_assoc, mul_inv_cancel_left, ← mul_assoc]
  unfold ratAd
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, one_mul]

set_option maxHeartbeats 1000000 in

theorem isPt_dia (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : Ch → GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl)
    {f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {J : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel B.host.F B.host.E B.sp.cm.sig J (B.T u) f bad) (hL : S.Lb = Lb (chOf c))
    (v : HeightOneSpectrum (𝓞 B.host.F)) (hv : (B.T u : 𝓞 B.host.F) ∈ v.asIdeal) (hP : v = P.1.under (𝓞 B.host.F))
    (hs : ∀ t t' : latS (F := B.host.F) (v.adicCompletion B.host.F) (intV B.host.E v)
        (Submodule.span (𝓞 B.host.E) (dualSet (B.sp.cm.sig : B.host.E →+* B.host.E) J S.Lb)),
      t'.1 = inclE (F := B.host.F) (v.adicCompletion B.host.F) ((X.piT u : 𝓞 B.host.E) : B.host.E) • t.1 → S.fT v hv t' = 0)
    (z : ℤ) (hz : (z : 𝓞 B.fields.E ⧸ P.1.asIdeal) = s) (δ : UPts B.sp.cm.sig J (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
    (hδ : IsDia S v hv z δ) : PtOf (y c * δ.1 * k (chOf c)) (dp I u a i P s c).1.1 := by
  classical
  have hX := FieldsLaws.fields_ok B
  have hPr := l.pr
  have hover : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w.under (𝓞 B.host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 := fun w hw =>
    (under_eq_iff B.host P.1 w).1 (hw.trans hP)
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.diamondElement_integral_support_lastRow _ _ B.sp.cm _ _ _ _ J S (X.piT u) P.1 v hv z δ hJ hP.symm hover
    (decoFin_mem_of_mem_divs P.2) (hPr.piT_notMem_sq hX u P.2) (conj_piT_notMem hPr u P)
    (fun x => by rw [hL]; exact h.lb _ x) hs hδ
  obtain ⟨p₀, hp₀, hN⟩ := h.k_std (chOf c)
  have hdis : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_left.2 fun w hw hw' => by
    obtain ⟨j, hj⟩ := exists_g_mem hPr ⟨w, hw⟩
    exact GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hw' (hPr.g_prime j) (hI.g_mem j) hj
  have hT : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w.under (𝓞 B.host.F) = v → (B.T u : 𝓞 B.host.E) ∈ w.asIdeal := fun w hw => by
    rw [← hw] at hv
    have h1 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.asIdeal := hv
    rwa [map_natCast] at h1
  refine GlobalTheory.T.isPointOf_last_coordinate_dilation_one_prime _ _ B.sp.cm _ _ _ _ (y c) δ.1 (k (chOf c)) ((I.stp u a i).rep c).1.1 _ P s _
    ((h.pt c).of_extTo (I.Q_subset_SQ a) hdis) hp₀.uni (by subst hJ; exact δ.2) (hN ▸ hp₀.lat) d1 d2
    (fun w hw => d3 w fun e => ?_) (h.k_T _ P) (fun r j hr => hz ▸ d4 r j hr) ?_ ?_
  · rcases hw with hw | hw | ⟨hw, hne⟩
    · exact T_notMem_vGs hPr u ⟨w, hw⟩ (hT w e)
    · exact GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hw (hPr.T_prime u) (hI.T_mem u) (hT w e)
    · rcases hover w e with e' | e'
      · exact hne e'
      · refine conj_piT_notMem hPr u P ?_
        have h1 : X.piT u ∈ w.asIdeal := decoFin_mem_of_mem_divs hw
        rw [e'] at h1
        exact h1
  · exact congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u i => q.1.1.deco) (mv_dia _ P s)
  · exact (congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u i => q.1.1.fr) (mv_dia ((I.stp u a i).rep c) P s) :)

set_option maxHeartbeats 4000000 in

theorem dilTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}), I.ReadsK l Z u a i hi chOf K → (∀ β, FunKilled (K β).lev (X.piT u)) → I.IdY l Z u a i hi eY → I.IdV l u a eV → DilationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY eV chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  intro B X I hI hPins l Z u a i hi bad Ch chOf K eY eV hR hs hY hV
  obtain ⟨k, hR⟩ := hR
  have hJ := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hPins l Z).2.2.2 i hi).1
  have hch : ∀ v s c, chOf ((I.fm l u a).dil i v s c) = chOf c := fun v s c =>
    (hR.key _ _).2 ⟨rfl, cosetIn_rep I l u a i v s c⟩
  have hy : ∀ β (c : {c // chOf c = β}), ((K β).y c).1 = ((K (chOf c.1)).y ⟨c.1, rfl⟩).1 := by
    rintro _ ⟨c, rfl⟩
    rfl
  have key : ∀ v (s : ((I.atT l u a).Fv v)ˣ) (z : ℤ), (z : (I.atT l u a).Fv v) = s → ∀ β (c : {c // chOf c = β}) δ,
      IsDia (K β).lev (eV v).1 (eV v).2 z δ → ∃ x : (K β).lev.U,
        ((K β).y c * δ).1 = bc (n := Fin ((I.rec7 l Z).R.N i)) (inclE (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
          (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))
          ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) *
            ((K β).y ⟨(I.fm l u a).dil i v s c.1, (hch v s c.1).trans c.2⟩).1 * x.1 ∧
        (((K β).lev.chi x : ℂˣ) : ℂ) =
          B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)) : B.LLˣ) : B.LL) := by
    rintro v s z hz _ ⟨c, rfl⟩ δ hδ
    have h1 := isPt_dia I hI l u a i hR v s c hJ (K (chOf c)).lev rfl (eV v).1 (eV v).2 (hV v) (hs _ _ _) z hz δ hδ
    obtain ⟨x, hx1, hx2⟩ := exists_level I l u a i hR v s c δ.1 h1 (chOf c) (hch v s c)
    refine ⟨x, ?_, hx2⟩
    rw [hy (chOf c) ⟨(I.fm l u a).dil i v s c, _⟩]
    exact hx1
  have hU : ∀ b (g : (I.stp u a i).G b), (I.stp u a i).gam b g ∈
      UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) := fun b g => by
    rw [hJ]
    show cT _ _ * 1 * _ = 1
    rw [mul_one]
    exact ((l.ch u a).step i).unit b g
  refine ⟨hch, fun v s z hz β c δ hδ => ?_, fun v s z hz β c δ hδ g hg => ?_⟩
  · obtain ⟨x, hx, -⟩ := key v s z hz β c δ hδ
    refine (DoubleCoset.eq _ _ _ _).2 ?_
    have hγ := hU c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))
    have hxU := (((K β).lev.U_eq x.1).1 x.2).1
    have hγ' : bc (n := Fin ((I.rec7 l Z).R.N i)) (inclE (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
        (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))
        ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) ∈
          UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := by
      have := mul_mem (mul_mem ((K β).y c * δ).2 (inv_mem hxU))
        (inv_mem ((K β).y ⟨(I.fm l u a).dil i v s c.1, (hch v s c.1).trans c.2⟩).2)
      rwa [hx, mul_inv_cancel_right, mul_inv_cancel_right] at this
    exact ⟨⟨_, hγ'⟩, ⟨_, hγ, rfl⟩, ⟨x.1, hxU⟩, x.2, Subtype.ext hx⟩
  · obtain ⟨x, hx, hc⟩ := key v s z hz β c δ hδ
    funext t
    have h1 := hg _ (hU c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) _ ((K β).y c * δ) x hx (eY t)
      (eY (frMul B.fields.emb B.embLL ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)))⁻¹ t)) (fun τ => by
        rw [hY, hY]
        have e := congrArg (fun q => q.1 τ) ((frEquiv B.fields.emb B.embLL
          ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)))).apply_symm_apply t)
        refine e.symm.trans ?_
        have e2 : embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := FieldsLaws.embLL_comp_emb B τ
        unfold Formalism.L2.Forms.atInf
        rw [← e2]
        rfl)
    rw [h1, hc]
    rfl

end GlobalTheory.Mem.Col2.DiaChart

end
