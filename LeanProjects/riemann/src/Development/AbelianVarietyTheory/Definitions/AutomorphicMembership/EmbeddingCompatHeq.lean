import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotRedDouble
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.LatticeGeometry.Inhabited
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnifStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSmulOfPreservesFrameOrbits

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.AsmCheck

variable {D : D7} {A : Amb D}

theorem tauEmb_injective (D : D7) : Function.Injective (DV.tauEmb D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem nonempty_cmList (A : Amb D) : Nonempty (CmList A) := by
  refine ⟨⟨Equiv.ofBijective (fun t => ⟨DV.tauEmb D t, A.cm t⟩) ⟨fun a b h => tauEmb_injective D (congrArg Subtype.val h), ?_⟩,
    fun _ => rfl⟩⟩
  rintro ⟨τ, hτ⟩
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
  rw [A.cmHost_rootComplex_eq_pm_sqrt, A.rt_eq] at hτ
  obtain ⟨t, ht⟩ := (exists_tauEmb_iff D g).2 (by
    have h1 : D.host.galE (D.host.sigmaOf g) = g :=
      (D.host.gal).apply_symm_apply g
    rw [← h1]
    exact (D.host.toHostAx.galE_mem_Psi_iff _).2 (D.host.φ₀.injective hτ))
  exact ⟨t, Subtype.ext ht.symm⟩

theorem cmList_unique (L L' : CmList A) : L = L' := by
  obtain ⟨a, ha⟩ := L
  obtain ⟨b, hb⟩ := L'
  obtain rfl : a = b := Equiv.ext fun t => Subtype.ext ((ha t).trans (hb t).symm)
  rfl

theorem card_tau (D : D7) : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.E / 2 := by
  have h1 := D.host.finrank_cmField
  have h2 : Nat.card D.what₂.Tau = _ := (Nat.card_congr D.eTau).trans (factCardPsi D.R D.host).1
  have h3 : Module.finrank ℚ D.host.E = 4 * D.R.ord := h1
  have h4 : Nat.card D.what₂.Tau = 2 * D.R.ord := h2
  rw [← Nat.card_eq_fintype_card, h3, h4]
  omega

section One

variable {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (C : CxSt D.what₂.LL)

theorem dim_flag (Φ : s.Flag) (k : s.Comp) : (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N := by
  rw [Φ.dim_eq, Formalism.DegreeFormula.dimFl, card_tau]

theorem exists_kit (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg) (Φ : s.Flag)
    (ρ : KeySec s.Xo κ.c) (X : PadPkg D N j s.Comp jC ng) :
    ∃ k : Kit s L C jC ng, k.Φ = Φ ∧ k.key = ρ ∧ k.pad.loc = X.loc :=
  ⟨{ Φ := Φ
     dim_eq := dim_flag s Φ
     key := ρ
     B := GlobalTheory.TrueCx.invariantB _ _ (GlobalTheory.TrueCx.first_index_eq_of_unfolded _ s.isUnf S.p_eq) _
     fl := fun _ _ => 1
     Mb := fun _ _ _ k => ⟨0, 1, fun σ => C.fsMet _ σ 0 (k := Empty) Empty.elim, 0, fun _ _ _ => 0⟩
     pad := { X with levIn := κ.inK }
     levIn := fun _ => Iff.rfl }, rfl, rfl, rfl⟩

theorem wtA_big (A : Amb D) {i : ℕ} (w : WeightFamilies.Wt D i) (t : D.what₂.Tau) (a : ℕ) :
    wtA w (DV.tauEmb D t, a) = ext0 (w.aP t) a := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · have : ¬ DV.tauEmb D t = conjEmb (DV.tauEmb D t) := fun h =>
      GlobalTheory.AllWt.conj_not_mem (H := A.H) ⟨_, A.cm t⟩ (h ▸ A.cm t)
    simp [this]
  · intro b _ hb
    have h1 : ¬ DV.tauEmb D t = DV.tauEmb D b := fun h => hb (tauEmb_injective D h).symm
    have h2 : ¬ DV.tauEmb D t = conjEmb (DV.tauEmb D b) := fun h =>
      GlobalTheory.AllWt.conj_not_mem (H := A.H) ⟨_, A.cm b⟩ (h ▸ A.cm t)
    simp [h1, h2]
  · simp

theorem wtA_small (A : Amb D) {i : ℕ} (w : WeightFamilies.Wt D i) (t : D.what₂.Tau) (a : ℕ) :
    wtA w (conjEmb (DV.tauEmb D t), a) = ext0 (w.aM t) a := by
  classical
  unfold wtA
  have h2 : ∀ b, ¬ conjEmb (DV.tauEmb D t) = DV.tauEmb D b := fun b h =>
    GlobalTheory.AllWt.conj_not_mem (H := A.H) ⟨_, A.cm t⟩ (h ▸ A.cm b)
  rw [Finset.sum_eq_single t]
  · simp [h2]
  · intro b _ hb
    have h1 : ¬ conjEmb (DV.tauEmb D t) = conjEmb (DV.tauEmb D b) := fun h => by
      have := congrArg conjEmb h
      rw [GlobalTheory.AllWt.conjEmb_conjEmb, GlobalTheory.AllWt.conjEmb_conjEmb] at this
      exact hb (tauEmb_injective D this).symm
    simp [h1, h2]
  · simp

theorem wt_wtOfN {i : ℕ} (w : WeightFamilies.Wt D i) (hp : S.Dw.p = (D.R.sigW i).1) (hq : S.Dw.q = (D.R.sigW i).2) :
    S.wt L (wtOfN N w) = GlobalTheory.AllWt.weightOf S.Dw (fun x => (wtA w x : ℤ)) ((w.n / 2 : ℕ) : ℤ) := by
  funext τ a
  obtain ⟨t, rfl⟩ := L.ψ.surjective τ
  have ha := a.2
  show wtOfN N w (L.ψ.symm (L.ψ t)) (Fin.cast S.rank_eq a) = _
  rw [Equiv.symm_apply_apply]
  simp only [GlobalTheory.AllWt.weightOf, L.ψ_val, wtA_big A, wtA_small A, wtOfN, Fin.val_cast, ext0]
  by_cases h : (a : ℕ) < (D.R.sigW i).1
  · rw [dif_pos h, if_pos (by omega), dif_pos h]
  · have h' : (a : ℕ) - (D.R.sigW i).1 < (D.R.sigW i).2 := by omega
    have h'' : S.Dw.q - 1 - ((a : ℕ) - S.Dw.p) < (D.R.sigW i).2 := by omega
    rw [dif_neg h, dif_pos h', if_neg (by omega), dif_pos h'']
    congr 4
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

theorem Lw_wtOfN {i : ℕ} (w : WeightFamilies.Wt D i) (hp : S.Dw.p = (D.R.sigW i).1) (hq : S.Dw.q = (D.R.sigW i).2)
    (Φ : s.Flag) (k : s.Comp) : s.Lw L Φ k (wtOfN N w) = (Φ.C k).LEx (exKey S.Dw (wtA w) w.n) := by
  rw [← GlobalTheory.ShFam.FlagCheck.Lw_weightOf, ← wt_wtOfN L w hp hq]
  rfl

end One

theorem trRul_rfl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m : MD H}
    {c c' : Coeff m.1} (hle : c.F ≤ c'.F) (f : Rul m.2.2 c) :
    trRul (rfl : m = m) hle f = GlobalTheory.FieldBC.rulBC hle f := rfl

section Comparison₂

variable {T : Top D} {h : LawsP T} {F : SrcFam (ambOf T.Q h.pins.1)} {t : ParTie T.Q h.pins.1 F}
  {L : CmList (ambOf T.Q h.pins.1)} {C : CxSt D.what₂.LL} {K : CutSt C} {R : ResSt C}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {k : Kits F L C jC ng}

include t in

theorem level_eq : T.Q.l = F.κg.l :=
  congrArg Sigma.fst (t.same 1 ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩)

theorem types_eq {P : FormsOver K R k} (hP : FormsAre h t K R k P) :
    P.KO = T.Q.c.F ∧ ∀ j w, P.Cusp j w = (recB h.toLawsCore).Cusp j w :=
  ⟨congrArg WeightFamilies.Prov.KO hP.base, fun j w => congrArg (fun B : WeightFamilies.Prov D => B.Cusp j w) hP.base⟩

theorem range_cmp {P : FormsOver K R k} (hP : FormsAre h t K R k P) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    Set.range (fun (f : P.Cusp j w) i => P.cmp j w i f) =
      Set.range (fun (f : (recB h.toLawsCore).Cusp j w) i => cmpAt h t k hj w.n i f.1) := by
  have e := (types_eq hP).2 j w
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨cast e f, funext fun i => (hP.cmp j hj w i f _ (cast_heq e f).symm).symm⟩
  · rintro ⟨f, rfl⟩
    exact ⟨cast e.symm f, funext fun i => hP.cmp j hj w i _ f (cast_heq e.symm f)⟩

theorem exists_place {P : FormsOver K R k} (hP : FormsAre h t K R k P) (la : HeightOneSpectrum (𝓞 P.KO)) :
    ∃ la' : HeightOneSpectrum (𝓞 T.Q.c.F), HEq la la' := by
  have e : HeightOneSpectrum (𝓞 P.KO) = HeightOneSpectrum (𝓞 T.Q.c.F) :=
    congrArg (fun B : WeightFamilies.Prov D => HeightOneSpectrum (𝓞 B.KO)) hP.base
  exact ⟨cast e la, (cast_heq e la).symm⟩

theorem pt_nonempty {P : FormsOver K R k} (hP : FormsAre h t K R k P) {j : ℕ} (hj : InR D j)
    (la : HeightOneSpectrum (𝓞 P.KO)) : Nonempty (P.Pt j la) := by
  obtain ⟨la', hl⟩ := exists_place hP la
  obtain ⟨e, -⟩ := hP.pts j hj la la' hl
  exact (recPJ_pt_nonempty h j hj la').map e.symm

end Comparison₂

section More

theorem parTie_par (F : SrcFam A) : ParTie F.par F.pins.1 F := ⟨fun _ _ => rfl, F.cs_le _⟩

theorem primes_first (F : SrcFam A) : F.κg.primes = Finset.univ.image D.host.g := by
  have hM : F.κg.l.M' = D.host.g 0 * D.host.g 1 := by rw [Level.M', F.κg_M, F.κg_A, Nat.lcm_one_right]
  rw [Lv.primes, hM, Nat.primeFactors_mul (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero,
    (D.host.g_prime 0).primeFactors, (D.host.g_prime 1).primeFactors]
  ext p
  simp [Fin.exists_fin_two, eq_comm]

theorem not_parTie {Q : Par D} {h : Q.PinHost} {F : SrcFam (ambOf Q h)} (hA : Q.l.A ≠ 1) : ¬ ParTie Q h F := fun t =>
  hA ((congrArg (fun m : MD Q.H => m.1.A) (t.same 1 ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩)).trans F.κg_A)

theorem embedding_compat_heq {B B' : WeightFamilies.Prov D} (hB : B = B') (kL : B.KO →+* D.what₂.LL)
    (h1 : ∀ x : 𝓞 B.KO, kL (x : B.KO) = D.what₂.OtoLL (B.eO x)) (ι : B'.KO →+* ℂ)
    (h2 : ∀ x : 𝓞 B'.KO, D.what₂.embLL (D.what₂.OtoLL (B'.eO x)) = ι (x : B'.KO)) (x : B.KO) (x' : B'.KO)
    (hx : HEq x x') : D.what₂.embLL (kL x) = ι x' := by
  subst hB
  cases hx
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 B.KO) x
  have e : ∀ y : 𝓞 B.KO, D.what₂.embLL (kL (algebraMap _ B.KO y)) = ι (algebraMap _ B.KO y) := fun y =>
    (congrArg D.what₂.embLL (h1 y)).trans (h2 y)
  rw [map_div₀, map_div₀, map_div₀, e, e]

variable {T : Top D} {h : LawsP T} {F : SrcFam (ambOf T.Q h.pins.1)}
  {L : CmList (ambOf T.Q h.pins.1)} {C : CxSt D.what₂.LL} {K : CutSt C} {R : ResSt C}
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} {k : Kits F L C jC ng}

theorem kL_of_base {P : FormsOver K R k} (hP : P.toWeightFamilies = recB h.toLawsCore) (x : P.KO) (x' : T.Q.c.F)
    (hx : HEq x x') : D.what₂.embLL (P.kL x) = (x' : ℂ) :=
  embedding_compat_heq hP P.kL P.kL_eO T.Q.c.F.val.toRingHom h.pins.2.2.1 x x' hx

end More

section FromFlags

def padAny (N j : ℕ) (hj : j ≤ N) (Comp : Type) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) :
    PadPkg D N j Comp jC ngJunk :=
  { padJunk D N j hj jC with
    Pt := Empty
    compPt := fun y => y.elim
    phiDR := fun _ y => y.elim
    phiMod := fun _ y => y.elim
    phiFr := fun _ y => y.elim
    phiFr_unram := fun _ y => y.elim
    normDetT := fun _ _ y => y.elim
    normDetH := fun _ _ y => y.elim
    htDetT := fun _ _ _ => 0 }

theorem two_lt_half (D : D7) : 2 < Module.finrank ℚ D.host.E / 2 := by
  have h3 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h : 2 ^ 2 ≤ D.R.ord := (Nat.pow_le_pow_right two_pos D.host.two_le_e).trans D.R.toFrame.two_pow_le_ord
  omega

theorem nonempty_key {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) : Nonempty (KeySec s.Xo κ.c) :=
  GlobalTheory.T.exists_key_section_unif _ _ _ _ _ _ _ _ (s.U κ.σ₀) κ.good_σ₀ s.isUnf
    (fun _ => GlobalTheory.OrbitScalar.exists_mem_dom _) (s.unf _ κ.good_σ₀).2.2.1 s.geo S.two_le (two_lt_half D)

theorem nonempty_kits_iff (F : SrcFam A) (L : CmList A) (C : CxSt D.what₂.LL)
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) :
    Nonempty (Kits F L C jC ngJunk) ↔ ∀ N j hN hj (κ : Lv A), Nonempty (F.src N j hN hj κ).Flag :=
  ⟨fun ⟨k⟩ N j hN hj κ => ⟨(k N j hN hj κ).Φ⟩, fun H => ⟨fun N j hN hj κ =>
    (exists_kit _ L C jC ngJunk (H N j hN hj κ).some (nonempty_key _).some (padAny N j hj _ jC)).choose⟩⟩

end FromFlags

end GlobalTheory.ShFam.AsmCheck
