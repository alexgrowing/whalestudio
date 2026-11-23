import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open scoped TensorProduct Matrix ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsObj

open GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting hiding levJ

section Space

variable {D : D7}

theorem gramAt_posDef {V : HSp D} (hp : V.IsPosDef) (hs : V.SigOK) (τ : D.what₂.Tau) : (gramAt D V τ).PosDef := by
  have := hs (tauE D τ)
  rw [hp] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem exists_compact_of_fin (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)}
    (hC : IsCompact C) : ∃ K : Set (GA D V), IsCompact K ∧ ∀ k : GA D V, (∀ i j, (finHom V k).1 i j ∈ C) → k ∈ K := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  choose R hR using fun τ => GlobalTheory.DefiniteQuotient.exists_bound_unitary (hV τ)
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k hk => hKe k fun i j => hCe' _ (hk i j) fun τ => ?_⟩
  have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
  have hu : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k) * V.gram.map (incA D) * Formalism.L2.Theta.mt V k = V.gram.map (incA D) := k.2
  have e : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V k)).map ((θ τ).comp (infPart D)) =
      ((Formalism.L2.Theta.mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
    ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
  have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
  simp only [Matrix.map_mul, e, hJ] at this
  exact ((hR τ _ this i j).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))

theorem finite_stab (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V))
    {C : Set (Af D.host.F ⊗[D.host.F] D.host.E)} (hC : IsCompact C) (hJ : ∀ k ∈ J, ∀ i j, k.1.1 i j ∈ C) (g : Bridge.Gf V) :
    Finite (Bridge.stab (Bridge.ratF V) J g) := by
  obtain ⟨-, -, h2, -, hg, hd, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_fin V hV hC
  obtain ⟨x, rfl⟩ := (finHom V).rangeRestrict_surjective g
  have hK' : IsCompact ((fun k => x * k * x⁻¹) '' K) := hK.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hcl : IsClosed (GQ V : Set (GA D V)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : GQ V → GA D V) ⁻¹' ((fun k => x * k * x⁻¹) '' K)).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK').finite_of_discrete
  refine Set.Finite.subset hfin fun γ hγ => ⟨x⁻¹ * γ.1 * x, hKe _ ?_, by group⟩
  have h := hJ _ ((Bridge.mem_stab _).1 hγ)
  rw [map_mul, map_mul, map_inv]
  exact h

theorem exists_cover_of_compact {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G)
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) {C : Set G} (hC : IsCompact C)
    (hCe : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) :
    ∃ (m : ℕ) (c : Fin m → H), ∀ g, ∃ (a : Fin m) (γ : Γ) (k : J), g = π.comp Γ.subtype γ * c a * k := by
  obtain ⟨S, -, hS⟩ := hC.elim_nhds_subcover (fun x => {y | π (x⁻¹ * y) ∈ J}) fun x _ =>
    (ho.preimage (continuous_const_mul x⁻¹)).mem_nhds (by simp)
  refine ⟨_, fun a => π (S.equivFin.symm a).1, fun g => ?_⟩
  obtain ⟨x, rfl⟩ := hπ g
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hCe x
  obtain ⟨s, hs, hcs⟩ := Set.mem_iUnion₂.1 (hS hc)
  exact ⟨S.equivFin ⟨s, hs⟩, ⟨γ, hγ⟩, ⟨_, hcs⟩, by simp [mul_assoc]⟩

theorem exists_cover (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (Bridge.Gf V)) (ho : IsOpenLev V J) :
    ∃ (m : ℕ) (c : Fin m → Bridge.Gf V), ∀ g, ∃ (a : Fin m) (γ : GQ V) (k : J), g = Bridge.ratF V γ * c a * k :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  (GlobalTheory.DefiniteQuotient.exists_compact V hV).elim fun _ h =>
    exists_cover_of_compact (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective J ho h.1 h.2

theorem isOpenLev_of_finCong (V : HSp D) {J : Subgroup (Bridge.Gf V)} {N : ℕ} (hN : 0 < N)
    (hK : ∀ k : GA D V, GlobalTheory.Member.FinCong V N k → fin V k ∈ J) : IsOpenLev V J := by
  obtain ⟨-, -, -, -, hg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN) hK)

theorem exists_split_system (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) {J : Subgroup (Bridge.Gf V)} {N₀ : ℕ} (hN₀ : 0 < N₀)
    (hK : ∀ k : GA D V, GlobalTheory.Member.FinCong V N₀ k → fin V k ∈ J) {N : ℕ} (hN : 0 < N) :
    ∃ (m : ℕ) (h : Fin m → GA D V), (∀ a, h a ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V (h a)).1) ∧
      Bridge.IsReps (Bridge.ratF V) J fun a => fin V (h a) := by
  obtain ⟨m, c, hc⟩ := exists_cover V hV J (isOpenLev_of_finCong V hN₀ hK)
  choose h hs he using fun a => GlobalTheory.SplitReps.exists_split_rep V hN₀ (fun k _ hk => hK k hk) hN (c a)
  have hr : Equivalence fun g g' : Bridge.Gf V => ∃ (γ : GQ V) (k : J), g = Bridge.ratF V γ * g' * k :=
    ⟨fun g => ⟨1, 1, by simp⟩, by
      rintro g g' ⟨γ, k, rfl⟩
      exact ⟨γ⁻¹, k⁻¹, by simp [mul_assoc]⟩, by
      rintro g g' g'' ⟨γ, k, rfl⟩ ⟨γ', k', rfl⟩
      exact ⟨γ * γ', k' * k, by simp [mul_assoc]⟩⟩
  obtain ⟨n, f, hf⟩ := GlobalTheory.UnRep.FullReps.exists_subfamily _ hr fun a => fin V (h a)
  refine ⟨n, fun a => h (f a), fun a => hs _, fun g => ?_⟩
  obtain ⟨a, ha⟩ := hc g
  exact hf g a (hr.trans ha (he a))

theorem finite_stab_of_le {V : HSp D} (hV : ∀ τ, (gramAt D V τ).PosDef) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Lat V}
    (hβ : IsSDFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {J : Subgroup (Bridge.Gf V)} (hle : J ≤ (levEnv V β L).J)
    (g : Bridge.Gf V) : Finite (Bridge.stab (Bridge.ratF V) J g) := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  rw [← GlobalTheory.PrincInLevel.eq_latC hβ] at hfg hsp
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.StabCompact.exists_compact_entries D.host.F D.host.E Λ hfg hsp
  exact finite_stab V hV J hC (fun k hk => hCe _ fun y hy => GlobalTheory.RepsCompare.mulVec_mem_hat hβ L (hle hk) hy) g

end Space

section Levels

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T)

theorem exists_isBad {N : ℕ} (hN : 0 < N) : ∃ bad : ℕ, IsBad L t bad ∧ N ∣ bad := by
  classical
  refine ⟨N * ∏ PP ∈ L.Pg ∪ L.Q t, Ideal.absNorm PP.asIdeal, ⟨Nat.mul_pos hN (Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)), fun PP hPP => ?_⟩, dvd_mul_right _ _⟩
  obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) (Finset.mem_union.2 hPP)
  rw [hu, Nat.cast_mul, Nat.cast_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))

theorem exists_isAdReps (hβ : IsSDFrame (Vc D i) (L.βV i) (L.ΛV i) 1) (hp : (Vc D i).IsPosDef) {bad : ℕ} (hb : IsBad L t bad)
    {M : ℕ} (hM : 0 < M) : ∃ (n : ℕ) (h : Fin n → GA D (Vc D i)) (gam : Fin n → ℕ),
      IsSubLev (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) 1 ∧
      IsAdReps (Vc D i) (L.ΛV i) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) bad (fun a => fin _ (h a))
        (fun a => Bridge.hLat (Vc D i) (fin _ (h a))) gam ∧
      IsLatReps (Vc D i) (L.ΛV i) bad (fun a => Bridge.hLat (Vc D i) (fin _ (h a))) ∧
      ∀ a, GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (bad * M) (finHom (Vc D i) (h a)).1 := by
  have hV := gramAt_posDef hp (D.sp.V_sig _)
  obtain ⟨n, h, h1, h2⟩ := exists_split_system (Vc D i) hV (J := GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) hb.1
    (fun k hk => GlobalTheory.PrincInLevel.finCong_mem_levEnv D (Vc D i) (L.βV i) (L.ΛV i) (L.datVt i t) bad k hβ hb.2 hk)
    (Nat.mul_pos hb.1 hM)
  have H : IsAdReps (Vc D i) (L.ΛV i) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) bad (fun a => fin _ (h a))
      (fun a => Bridge.hLat (Vc D i) (fin _ (h a))) _ :=
    ⟨h2, fun a => (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).2 (GlobalTheory.SplitReps.suppSplit_mono (dvd_mul_right _ _) (h1 a).2),
      fun a => (GlobalTheory.RepsCompare.isTransl_iff hβ _ _).2 rfl,
      fun a => ⟨finite_stab_of_le hV hβ (L.datVt i t) le_rfl _, rfl⟩⟩
  exact ⟨n, h, _, ⟨le_rfl, by simp, GlobalTheory.RepsCompare.isOpenLev_levEnv hβ (L.datVt i t) hb.1 hb.2, by simp⟩, H,
    GlobalTheory.RepsCompare.isLatReps_of_isAdReps hβ (L.datVt i t) le_rfl H, fun a => (h1 a).2⟩

theorem repsAt (hβ : IsSDFrame (Vc D i) (L.βV i) (L.ΛV i) 1) (hp : (Vc D i).IsPosDef) {N : ℕ} (hN : 0 < N) : RepsAt L i t N := by
  obtain ⟨bad, hb, hd⟩ := exists_isBad L t hN
  obtain ⟨n, h, gam, h1, h2, h3, -⟩ := exists_isAdReps L i t hβ hp hb one_pos
  exact ⟨n, _, _, bad, _, gam, 1, hb, hd, h1, h2, h3⟩

def RepsGeomAt {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (N : ℕ) : Prop :=
  ∃ (n : ℕ) (h : Fin n → Bridge.Gf (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ) (Lh : Fin n → Lat (Vc D i))
    (gam : Fin n → ℕ) (vol : ℝ) (La : Fin n → GenLat D.host.E (Vc D i).rank) (Nc : Fin n → ℕ),
    IsBad L t bad ∧ N ∣ bad ∧ IsSubLev (Vc D i) (GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.levJ L i t) J' vol ∧
      IsAdReps (Vc D i) (L.ΛV i) J' bad h Lh gam ∧ IsLatReps (Vc D i) (L.ΛV i) bad Lh ∧
      RepsOK (l := l) bad La Nc gam ∧ LatPin Lh La

theorem isPosDef_of_vStd (hV : VStd D i) : (Vc D i).IsPosDef := fun τ => by
  have h := factVSig _ _ D.sp ((i : ℕ) + 1) (by omega) (by omega) τ
  rw [GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hV, if_neg Bool.false_ne_true] at h
  rw [D.sp.V_rank _ (by omega) i.2]
  exact h

end Levels

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

def ChoiceWithReps (D : D7) : Prop :=
  ∀ C : Formalism.L2.Host.CharFrame D, ∃ L : LevCh D Unit, L.C = C ∧ L.Is () ∧
    ∀ (i : Fin D.R.m) (N : ℕ), 0 < N → RepsAt L i () N ∧
      ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H), RepsGeomAt L i () l N

theorem row : Row := fun _ _ _ _ _ _ _ _ _ _ _ R hL hp i t _ hN => repsAt R.toLevCh i t (hL.βV i) (hp i) hN

section Record

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (K' : Type) [Field K']

def RepsEx : Prop :=
  ∀ (t : T0) (b : ℕ), 0 < b →
    ∃ (Cl : Type) (_ : Fintype Cl) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))) (bad : ℕ)
      (Lh : Cl → Lat (Vc D i)) (gam : Cl → ℕ) (vol : K'),
      RepsR R i t h bad J' Lh gam vol ∧ b ∣ bad ∧ (∀ k, 0 < gam k) ∧ vol ≠ 0

def RepsAll : Prop :=
  ∀ (t : T0) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i))), bad ≠ 0 →
    (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → J' ≤ levJ R i t →
    IsOpen (J' : Set (Bridge.Gf (Vc D i))) →
    ∃ (n : ℕ) (h : Fin n → GA D (Vc D i)) (Lh : Fin n → Lat (Vc D i)) (gam : Fin n → ℕ) (vol : K'),
      RepsR R i t h bad J' Lh gam vol ∧ (∀ k, 0 < gam k) ∧ (CharZero K' → vol ≠ 0)

def RepsExCov : Prop :=
  ∀ {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
    {Tp : Type} (tup : Tp → T0) (dδ : Tp → DeltaDat Xo c (Vc D i).rank),
    ∃ (Cl : Tp → Type) (_ : ∀ t, Fintype (Cl t)) (h : ∀ t, Cl t → GA D (Vc D i))
      (J' : Tp → Subgroup (Bridge.Gf (Vc D i))) (bad : Tp → ℕ)
      (Lh : ∀ t, Cl t → Lat (Vc D i)) (gam : ∀ t, Cl t → ℕ) (vol : Tp → K')
      (La : ∀ t, Cl t → GenLat D.host.E (Vc D i).rank) (Nc : ∀ t, Cl t → ℕ),
      (∀ t, RepsR R i (tup t) (h t) (bad t) (J' t) (Lh t) (gam t) (vol t) ∧ vol t ≠ 0) ∧
      (∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1)) ∧
      RepsCov Xo c Cl dδ bad Lh La Nc gam

end Record

end GlobalTheory.RepsObj

end
