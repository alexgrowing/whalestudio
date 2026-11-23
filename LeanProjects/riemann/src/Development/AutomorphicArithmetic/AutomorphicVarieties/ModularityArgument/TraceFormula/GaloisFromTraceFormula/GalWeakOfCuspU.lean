import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.UnrRecOfHasSat

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rig PositivityTheory.Rg.BcB.F.Rig.GalX
open GlobalTheory.HeckeGal.Model (absPow absPow_isAbsPow)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

def GalAt (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (N : ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a ≤ N → ∀ P : CuspSub E a, P.IsCsd → ∀ s : ℝ, (CG.mk (P.twist (absPow E s))).IsRegAlg →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), (P.twist (absPow E s)).IsLocComp w σ →
        ∀ S : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω),
          IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
          (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
            X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-((1 - (a : ℝ)) / 2) : ℝ) : ℂ)))).prod

def GalWeak (N : ℕ) : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∃ (l : ℕ) (_ : Fact l.Prime) (ι : Qbar l ≃+* ℂ), GalAt E (AlgebraicClosure E) ι N

private theorem sideW (hS : StrSat) (hSt : Strings) (hC : CuspCsd) {E : Type} [Field E] [NumberField E] [IsCMField E] (Ω : Type) [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N n : ℕ} (hG : GalAt E Ω ι N) (hN' : n ≤ N) (D : Pre E n)
    (hr : D.Reg) (ht : D.ThetaStable) :
    ∃ (m : ℕ) (R : G E Ω →* GL (Fin m) (Qbar l)), Continuous R ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        (∃ B, D.Sat w B) ∧ ∀ B, D.Sat w B → ∀ (A : ValuationSubring Ω) (g : G E Ω),
          IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) g →
          (R (g ^ (-1 : ℤ))).val.charpoly = (B.map fun z : ℂˣ =>
            X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod := by
  classical
  choose a d P ha hd hu hn hemb using hSt E n D hr
  have he : ∀ i, AscEmb (D.V i) (P i) (d i) := fun i => hemb i (P i) (Setoid.refl (α := CuspSub E (a i)) (P i))
  have hcsd : ∀ i, (P i).IsCsd := fun i =>
    hC E n D hr ht i (a i) (d i) (P i) (ha i) (hd i) (hu i) (hn i) (he i)
  have hle : ∀ i, a i ≤ N := fun i => by
    obtain ⟨h, -⟩ := he i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    have h1 : D.N i ≤ n := (Finset.single_le_sum (f := D.N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D.h.le
    have h2 : a i ≤ d i * a i := Nat.le_mul_of_pos_left _ (hd i)
    omega
  let s : (Σ i : Fin D.c, Fin (d i)) → ℝ := fun x => spehExp (d x.1) x.2 + ((a x.1 : ℝ) - n) / 2
  have hreg : ∀ x : (Σ i : Fin D.c, Fin (d i)), (CG.mk ((P x.1).twist (absPow E (s x)))).IsRegAlg :=
    fun x => regTw D hr x.1 (P x.1) (he x.1) x.2
  choose r hrc hrf using fun x : (Σ i : Fin D.c, Fin (d i)) =>
    hG (a x.1) (ha x.1) (hle x.1) (P x.1) (hcsd x.1) (s x) (hreg x)
  let e := Fintype.equivFin (Σ x : (Σ i : Fin D.c, Fin (d i)), Fin (a x.1))
  refine ⟨_, GlobalTheory.BlockSum.blockRep e r, GlobalTheory.BlockSum.continuous_blockRep e r hrc, ?_⟩
  have hev := Filter.eventually_all.2 fun i => hS E (D.N i) (a i) (d i) (D.V i) (P i) (D.σ i) (D.pos i)
    (D.discrete i) (hu i) (hn i) (he i) (D.loc i) (fun k => absPow E (spehExp (d i) k))
    (fun k => absPow_isAbsPow E _)
  filter_upwards [hev, Filter.eventually_all.2 hrf] with w hw hrw hl
  choose b hb hsph hsat using hw
  refine ⟨⟨_, fun i => ∑ k, b i k, fun i => ⟨hsph i, hsat i⟩, rfl⟩, ?_⟩
  rintro _ ⟨b', hb', rfl⟩ A g hA hg
  have hbb : ∀ i, b' i = ∑ k, b i k := fun i => (hb' i).2.unique (hsat i)
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hx : ∀ x : (Σ i : Fin D.c, Fin (d i)), (r x (g ^ (-1 : ℤ))).val.charpoly = ((b x.1 x.2).map fun z : ℂˣ =>
      X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod := by
    rintro ⟨i, k⟩
    have h1 := (CG.HasSat.twist_absPow (hb i k) (((a i : ℝ) - n) / 2)).1
    rw [twist_absPow_absPow] at h1
    obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E (a i)
      ((P i).twist (absPow E (s ⟨i, k⟩))) w
    have h2 : GlobalTheory.LFun.HasSatGL w σ.ρ _ :=
      (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.1 ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ (Fin (a i)) σ.V σ.ρ _).2
        (GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp _ h1 hσ))).2
    rw [hrw ⟨i, k⟩ hl σ hσ _ h2 A g hA hg, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun z _ => ?_)
    simp only [Function.comp_apply, Units.val_mul]
    rw [(absPow_isAbsPow E _).2.1 w, mul_assoc, ← Complex.cpow_add _ _ hN]
    refine congrArg (fun u : ℂ => X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ u))) ?_
    push_cast
    ring
  rw [GlobalTheory.BlockSum.charpoly_blockRep, Finset.prod_congr rfl fun x _ => hx x, Fintype.prod_sigma]
  simp only [hbb]
  rw [prod_map_sum]
  exact Finset.prod_congr rfl fun i _ => (prod_map_sum _ _ _).symm

theorem galStep_le {N : ℕ} (hW : GalWeak N) (E : Type) [Field E] [NumberField E] [IsCMField E] (hu : GlobalTheory.BCT.Unr E) (n : ℕ)
    (hn : n ≤ N) (D D' : Pre E n) (hr : D.Reg) (hr' : D'.Reg) (ht : D.ThetaStable) (ht' : D'.ThetaStable)
    (hsplit : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ D'.Sat w B) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ D'.Sat w B := by
  classical
  obtain ⟨l, _, ι, hG⟩ := hW E hu
  obtain ⟨m, R, hR, hev⟩ := sideW strSat strings_holds cuspCsd_holds (AlgebraicClosure E) ι hG hn D hr ht
  obtain ⟨m', R', hR', hev'⟩ := sideW strSat strings_holds cuspCsd_holds (AlgebraicClosure E) ι hG hn D' hr' ht'
  have hl2 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    have h20 : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    refine Filter.eventually_cofinite.2 ?_
    simpa only [not_not] using Formalism.L2.G.finite_setOf_mem_asIdeal (F := E) h20
  have hall := ((hev.and hev').and (hsplit.and hl2))
  obtain hT := Filter.eventually_cofinite.1 hall
  have hRam := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).2
  let f : G E (AlgebraicClosure E) → ℕ → Qbar l := fun g j => (R g⁻¹).val.charpoly.coeff j
  let f' : G E (AlgebraicClosure E) → ℕ → Qbar l := fun g j => (R' g⁻¹).val.charpoly.coeff j
  have hf : Continuous f := continuous_pi fun j =>
    (PositivityTheory.Rg.DzCong.CongruenceClosure.continuous_coeff_charpoly m j).comp (Units.continuous_val.comp (hR.comp continuous_inv))
  have hf' : Continuous f' := continuous_pi fun j =>
    (PositivityTheory.Rg.DzCong.CongruenceClosure.continuous_coeff_charpoly m' j).comp (Units.continuous_val.comp (hR'.comp continuous_inv))
  have hff : f = f' := GlobalTheory.Published.chebotarevDegreeOne'.eq_of_frob (hT.union hRam) hf hf'
    (fun v hv hd A hA σ hσ => by
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hv
      obtain ⟨B, hB, hB'⟩ := h3 (PositivityTheory.Rg.DzCong.CongruenceClosure.isSplitAt_of_deg_one v hd h5)
      have c1 := (h1 h4).2 B hB A σ hA hσ
      have c2 := (h2 h4).2 B hB' A σ hA hσ
      rw [_root_.zpow_neg_one] at c1 c2
      funext j
      simp only [f, f', c1, c2])
  filter_upwards [hev, hev', hl2] with w h1 h2 h4
  obtain ⟨B, hB⟩ := (h1 h4).1
  obtain ⟨B', hB'⟩ := (h2 h4).1
  obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure E) w
  obtain ⟨g, hg⟩ := Formalism.MainNotions.LatticeVariant.exists_isFrob A w hA
  have c1 := (h1 h4).2 B hB A g hA hg
  have c2 := (h2 h4).2 B' hB' A g hA hg
  have e : (R (g ^ (-1 : ℤ))).val.charpoly = (R' (g ^ (-1 : ℤ))).val.charpoly := by
    ext j
    have := congrFun (congrFun hff g) j
    simpa [f, f', _root_.zpow_neg_one] using this
  rw [c1, c2] at e
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  let ψ : ℂˣ → Qbar l := fun z => ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2))
  have hψ : Function.Injective ψ := fun z z' h => by
    have h' := ι.symm.injective h
    have hc : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2) ≠ 0 :=
      fun h0 => hN ((Complex.cpow_eq_zero_iff _ _).1 h0).1
    exact Units.ext (mul_right_cancel₀ hc h')
  have key : ∀ C : Multiset ℂˣ, (C.map fun z : ℂˣ =>
      X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod =
      ((C.map ψ).map fun u => X - Polynomial.C u).prod := fun C => by
    rw [Multiset.map_map]
    rfl
  have e2 := congrArg Polynomial.roots e
  rw [key, key, Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  have hBB : B = B' := Multiset.map_injective hψ e2
  exact ⟨B, hB, hBB ▸ hB'⟩

theorem galWeak_of_cuspU (hG : UpperTheory.GalN.CuspU) (hL : GlobalTheory.Published.LocalLanglandsGL) (N : ℕ) : GalWeak N := by
  intro E _ _ _ _
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  refine ⟨2, inferInstance, ι, fun a ha _ P hP s hr => ?_⟩
  obtain ⟨r, wt, HT, H⟩ := hG E (AlgebraicClosure E) 2 ι a ha _ _ hr (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s)
  refine ⟨r, H.cont, Filter.Eventually.of_forall fun w hl σ hσ S hS B g hB hg => ?_⟩
  obtain ⟨rc, hrc⟩ := (hL.1 E _ B w hB).exists
  refine GlobalTheory.T.local_langlands_galois_compat E _ 2 ι a r H.cont w hl B hB rc hrc σ S hS _ ((H.aw hl hrc hσ).eq_unr ?_) g hg
  exact (GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 (UpperTheory.GalN.unr_rec_of_hasSat hrc σ S hS)

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
