import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ApartOfNotMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.WtDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.OpenCompactMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.LacunaryBaseWeightAntitone
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ExistsTestOp
import Development.AbelianVarietyTheory.Definitions.Divisors.CongWtLvLac
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW
open GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Cong

def EllSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∀ N ∈ nhds (1 : GL (Fin a) (w₀.adicCompletion E)), ∀ m₀ : ℕ,
    ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m))), m₀ ≤ m ∧
      (J : Set (GL (Fin a) (w₀.adicCompletion E))) ⊆ N ∧ IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧
      Function.Surjective θ ∧ ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 →
        ∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
          (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ

open UpperTheory.Gal.Gen in

def StepSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (v' : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → IsSplitAt v' → Apart v' w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → (∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' a → x ∈ K) →
    ∀ (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))), IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) →
    ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ),
      (∀ j, IntW ι lam (t j) ∧ Loc.IntL ι lam (t j)) →
      (∀ j, ∀ g ∈ (t j).support, (∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧ ∀ u, ¬ Apart u v' → cLoc u g = 1) →
      ActsBy (K ⊓ Kv.comap (cLoc v')) t η →
    ∀ τ₀ : E →+* ℂ, OverPl ι τ₀ v' → ∀ U, OfType lam (K ⊓ Kv.comap (cLoc v')) U →
      PolyApprox (fun j => ι.symm (η U j)) {ϑ | ∃ (U' : Submodule ℂ (UA E a → ℂ)) (mu : (E →+* ℂ) → DomWeight a),
        (∀ τ, mu τ ≠ lam τ → OverPair ι v' τ) ∧ GapWt a (mu τ₀) ∧ OfType mu K U' ∧ TyEll E l a w₀ U' ∧
        ϑ = fun j => ι.symm (η U' j)}

theorem not_apart_of_overPair {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    {u v : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (hu : OverPair ι u τ) (hv : OverPair ι v τ) : ¬ Apart u v := by
  obtain ⟨x, hx, hxu⟩ := exists_of_overPair ι hu
  obtain ⟨y, hy, hyv⟩ := exists_of_overPair ι hv
  have key : ∀ z : HeightOneSpectrum (𝓞 E), OverPl ι τ z → z.asIdeal = PlaceEmb.smallIdeal (ι.symm.toRingHom.comp τ) :=
    fun z hz => z.isMaximal.eq_of_le (PlaceEmb.smallIdeal_isPrime _).ne_top fun b hb => hz b hb
  obtain rfl : x = y := HeightOneSpectrum.ext ((key x hx).trans (key y hy).symm)
  exact GlobalTheory.Cong.AdaptLev.not_apart_trans (GlobalTheory.Cong.AdaptLev.not_apart_symm hxu) hyv

open UpperTheory.Gal.Gen in

theorem intL_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    {v' : HeightOneSpectrum (𝓞 E)} {lam mu : (E →+* ℂ) → DomWeight a} (h : ∀ τ, mu τ ≠ lam τ → OverPair ι v' τ)
    {f : UA E a →₀ ℂ} (hv : ∀ g ∈ f.support, ∀ u, ¬ Apart u v' → cLoc u g = 1) (hf : Loc.IntL ι lam f) : Loc.IntL ι mu f := by
  classical
  intro g hg
  obtain ⟨h1, d, h2, h3⟩ := hf g hg
  refine ⟨h1, d, h2, h3.trans_eq ?_⟩
  congr 2
  refine finsum_congr fun u => finsum_congr fun hu => Finset.sum_congr rfl fun τ hτ => ?_
  have : mu τ = lam τ := by
    by_contra hne
    exact hu.2 (hv g hg u (not_apart_of_overPair ι (Finset.mem_filter.1 hτ).2 (h τ hne)))
  rw [this]

open UpperTheory.Gal.Gen in
theorem stepSt_of_ex (hEll : EllSt) (H : WtLacEx) : StepSt := by
  intro E _ _ _ l _ ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam Jx t η ht htv hη τ₀ hτ₀ U hU
  have h1 := H E l ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam Jx t η (fun j => (ht j).2) htv hη τ₀ hτ₀ U hU
  refine (combine_holds (Qbar l) _ _ _ _ 1 h1 ?_).mono fun _ h => h.1
  rintro _ ⟨U₁, mu, g1, g2, g3, rfl⟩
  refine ⟨by simp, ?_⟩
  have hmu : (Wt.ofFam mu).at = mu := by
    obtain ⟨W', -, hW', -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a mu K U₁ hK.fin g3 w₀
    obtain rfl : mu = W'.at := (funext hW').symm
    have : Wt.ofFam W'.at = W' := funext fun v => W'.at_embedding v
    rw [this]
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := PlaceEmb.norm_p_lt_one
  have hD : Dense ι (Wt.ofFam mu) K fun U' => TyEll E l a w₀ U' := by
    intro f hf ε hε
    obtain ⟨N, hN, hfN⟩ := smoothAt_holds E a w₀ hs₀ _ f
    obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hε hl1
    obtain ⟨m, J, θ, hm, hJN, hJo, hJc, hJt, hθ, hsc⟩ := hEll E l a ha w₀ hw₀ N hN m₀
    have hfJ : f ∈ fixedBy (Wt.ofFam mu) (lev K w₀ J) := by
      intro c hc v g
      obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := ((levFacts_holds E a w₀ hs₀ K hK J hJo hJc).2.1 c).1 hc
      rw [← mul_assoc, hfN x hx (hJN hxJ), hf k hk]
    obtain ⟨G, hG, e, he, hGe⟩ := tyStep_holds E l ι a w₀ hs₀ K hK _ J hJo hJc hJt m θ f hfJ
    refine ⟨G, part_mono _ _ ?_ hG, e, fun g => (he g).trans
      ((pow_le_pow_of_le_one (norm_nonneg _) hl1.le hm).trans hm₀.le), hGe⟩
    rintro U' ⟨χ, hχ, φ, hφ, hφ0, -, hφJ⟩
    exact ⟨m, J, θ, χ, hJo, hJc, hJt, hθ, hχ, hsc χ hχ, φ, hφ, hφ0, hφJ⟩
  refine (toPolyX_holds E l ι a w₀ K hK.fin mu _ hD Jx t η
    (Loc.frame denomBdd_holds rhoBound_holds latFacts_holds levelEx_holds ι _ _ fun j => Or.inr (by
      rw [hmu]
      exact intL_congr ι g1 (fun g hg => (htv j g hg).2) (ht j).2))
    (fun V hV φ hφ hx j => hη V hV φ hφ (fun x h => hx x h.1) j) U₁ g3).mono ?_
  rintro _ ⟨U', k1, k2, rfl⟩
  exact ⟨U', mu, g1, g2, k1, k2, rfl⟩

open UpperTheory.Gal.Gen in
theorem congUWG_of (H : StepSt) (hFin : FinU) (D : ∀ a : ℕ, MvPolynomial (Fin a) ℤ) (hD : ∀ a, D a ≠ 0) :
    CongUWG TyEll (GenOf D) WtLac := by
  classical
  intro E _ _ _ l _ ι a ha T _ U hU w₀ v' hw₀ hs₀ hv' hsv hap
  obtain ⟨K, Kw, Kv, hK, hKvo, hfix, hKwv, hoc, hsph, hns, hKs⟩ := exists_level hU hs₀ hsv hap
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep E a U hU.1
  set K' := K ⊓ Kv.comap (cLoc v') with hK'def
  have hK' : IsLevelAway w₀ K' := isLevelAway_inf hK v' hKvo
  have hOf : OfType lam K' U := ⟨hU.1, hlam, hfix⟩
  have hone : ∀ {w u : HeightOneSpectrum (𝓞 E)}, Apart w u → ∀ x ∈ locU a w, ∀ u', ¬ Apart u' u → cLoc u' x = 1 := fun hwu x hx u' hu' =>
    ((GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx).2 u' (GlobalTheory.Cong.AdaptLev.apart_of_apart_not_apart hwu hu')
  have hKs' : ∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → ∀ x ∈ locU a w, x ∈ K' ↔ cLoc w x ∈ Kw w := fun w h1 h2 h3 x hx => by
    rw [← hKs w h1 h2 x hx]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show cLoc v' x ∈ Kv
    rw [hone h3 x hx v' (not_apart_self v')]
    exact one_mem _
  have hloc : ∀ U' : Submodule ℂ (UA E a → ℂ), (∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ) → ∀ w, IsSplitAt w → Apart w w₀ →
      Apart w v' → ∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ Kw w → RU E a x φ = φ :=
    fun U' ⟨φ, g1, g2, g3⟩ w h1 h2 h3 => ⟨φ, g1, g2, fun x hx h => g3 x ((hKs' w h1 h2 h3 x hx).2 h)⟩
  have hlev : ∀ U', IsAutRepU U' → (∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ) → HasLevelOff w₀ v' Kw U' :=
    fun U' h1 h2 w g1 g2 g3 σ hσ => fixed_ne_bot h1 g1 (hloc U' h2 w g1 g2 g3) σ hσ
  refine ⟨Kw, hlev U hU.1 hfix, hoc, fun w h1 _ h3 h4 => hsph w h1 h3 h4, fun Z W hZ hW => ?_⟩
  have hfin : ∀ {w} {f : UA E a →₀ ℂ}, (∀ g ∈ f.support, g ∈ locU a w) → ∀ g ∈ f.support, g ∈ finU E a :=
    fun h g hg => (Subgroup.mem_inf.1 (h g hg)).1
  have hhyp : ∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → HypAt K' w := fun w h1 h2 h3 h4 x hx => by
    rw [hKs' w h1 h2 h3 x hx, hsph w h1 h3 h4]
  choose tp htp hpact using fun p : W × ℤ => exists_powOp (a := a) (hW p.1.1 p.1.2).1 p.2
  choose cp hcp0 hcp using fun p : W × ℤ => exists_scale ι lam (tp p) (hfin (htp p))
  let Φ : MvPolynomial (Fin a) ℂ := MvPolynomial.map (Int.castRingHom ℂ) (D a)
  choose tz ez htz hzact using fun z : Z => exists_testOp K' (hZ z.1 z.2).1
    (hhyp z.1 (hZ z.1 z.2).1 (hZ z.1 z.2).2.1 (hZ z.1 z.2).2.2.1 (hZ z.1 z.2).2.2.2) Φ
  choose cz hcz0 hcz using fun z : Z => exists_scale ι lam (tz z) (hfin (htz z))
  refine ⟨fun w n => if h : w ∈ W then cp (⟨w, h⟩, n) else 1, fun w n => by
    dsimp only
    split_ifs
    exacts [hcp0 _, one_ne_zero], fun J O θ hθ => ?_⟩
  have hO₀ : ∀ j, Apart (O.pl j) w₀ := fun j => apart_of_not_mem hw₀ (O.away j)
  have hOv : ∀ j, Apart (O.pl j) v' := fun j => apart_of_not_mem hv' (O.away j)
  choose tj ej htj hjact hje using fun j => exists_op (O.split j) (Kw (O.pl j)) (hoc _ (O.split j) (hO₀ j)).1
    (hoc _ (O.split j) (hO₀ j)).2 (O.f j) (O.z j) (O.act j)
  have hsys : ∀ U', IsAutRepU U' → (∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ) → IsSysU O U' fun j => ι.symm (ej j U') :=
    fun U' h1 h2 j σ hσ => congrArg ι.symm (hje j U' h1 (hloc U' h2 _ (O.split j) (hO₀ j) (hOv j)) σ hσ)
  have hθeq : θ = fun j => ι.symm (ej j U) := funext fun j => by
    obtain ⟨σ, hσ⟩ := (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U hU.1 _ (O.split j)).1
    rw [hθ j σ hσ]
    exact (hsys U hU.1 hfix j σ hσ).symm
  have hactJ : ActsBy K' tj fun U' j => ej j U' := fun U' hU' φ hφ hx j =>
    hjact j U' hU' φ hφ fun x h1 h2 => hx x ((hKs' _ (O.split j) (hO₀ j) (hOv j) x h1).2 h2)
  subst hθeq
  refine ⟨?_, fun hq => hFin E l ι a ha w₀ K' hK' lam J tj (fun U' j => ej j U')
    (fun j g hg => ⟨(Subgroup.mem_inf.1 (htj j g hg).1).1, by rw [(htj j g hg).2]; exact hq j _⟩) hactJ U hOf⟩
  let t : (J ⊕ W × ℤ) ⊕ Z → (UA E a →₀ ℂ) := Sum.elim (Sum.elim tj fun p => cp p • tp p) fun z => cz z • tz z
  let η : Submodule ℂ (UA E a → ℂ) → (J ⊕ W × ℤ) ⊕ Z → ℂ := fun U' =>
    Sum.elim (Sum.elim (fun j => ej j U') fun p => cp p * PowSatU U' p.1 p.2) fun z => cz z * ez z U'
  have hact : ActsBy K' t η := by
    rintro U' hU' φ hφ hx ((j | p) | z)
    · exact hactJ U' hU' φ hφ hx j
    · obtain ⟨h1, h2, h3, h4⟩ := hW p.1.1 p.1.2
      show opOf (RU E a) (cp p • tp p) φ = (cp p * PowSatU U' p.1 p.2) • φ
      rw [opOf_smul', hpact p U' hU' φ hφ fun x g1 g2 => hx x ((hhyp _ h1 h2 h3 h4 x g1).2 g2), smul_smul]
    · show opOf (RU E a) (cz z • tz z) φ = (cz z * ez z U') • φ
      rw [opOf_smul', (hzact z U' hU').1 φ hφ hx, smul_smul]
  have hsupp : ∀ j, ∃ w, Apart w w₀ ∧ Apart w v' ∧ ∀ g ∈ (t j).support, g ∈ locU a w := by
    rintro ((j | p) | z)
    · exact ⟨_, hO₀ j, hOv j, fun g hg => (htj j g hg).1⟩
    · exact ⟨_, (hW p.1.1 p.1.2).2.1, (hW p.1.1 p.1.2).2.2.1, fun g hg => htp p g (Finsupp.support_smul hg)⟩
    · exact ⟨_, (hZ z.1 z.2).2.1, (hZ z.1 z.2).2.2.1, fun g hg => htz z g (Finsupp.support_smul hg)⟩
  have hint : ∀ j, IntW ι lam (t j) ∧ Loc.IntL ι lam (t j) := by
    rintro ((j | p) | z)
    · have key : ∀ g ∈ (tj j).support, g ∈ finU E a ∧ DenomLe l 0 g ∧ ‖ι.symm (tj j g)‖ ≤ 1 := fun g hg => by
        obtain ⟨h1, h2⟩ := htj j g hg
        refine ⟨(Subgroup.mem_inf.1 h1).1, fun u hu => ?_, by rw [h2]; exact O.int j _⟩
        have h3 : cLoc u g = 1 := hone (apart_of_not_mem hu (O.away j)) g h1 u (not_apart_self u)
        rw [h3, inv_one, pow_zero, one_smul, Units.val_one]
        refine ⟨fun i k => ?_, fun i k => ?_⟩ <;>
        · rw [Matrix.one_apply]
          split_ifs
          exacts [one_mem _, zero_mem _]
      exact ⟨fun g hg => ⟨(key g hg).1, 0, (key g hg).2.1, (key g hg).2.2.trans_eq (by simp)⟩,
        fun g hg => ⟨(key g hg).1, 0, (key g hg).2.1, (key g hg).2.2.trans_eq (by simp)⟩⟩
    · exact hcp p
    · exact hcz z
  have hlam' : (Wt.ofFam lam).at = lam := by
    obtain ⟨W', -, hW', -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam K' U hK'.fin hOf w₀
    obtain rfl : lam = W'.at := (funext hW').symm
    have : Wt.ofFam W'.at = W' := funext fun v => W'.at_embedding v
    rw [this]
  have hd : GenData w₀ K' Z fun _ => Φ :=
    ⟨fun w hw => (hZ w hw).1, fun w hw => (hZ w hw).2.1,
      fun w hw => hhyp w (hZ w hw).1 (hZ w hw).2.1 (hZ w hw).2.2.1 (hZ w hw).2.2.2,
      fun _ _ h => hD a (MvPolynomial.map_injective _ Int.cast_injective (h.trans (map_zero _).symm))⟩
  have h1 := toPolyX_holds E l ι a w₀ K' hK'.fin lam _ (denseGen_holds E l ι a ha w₀ hw₀ hs₀ K' hK' (Wt.ofFam lam) Z _ hd) _ t η
    (frameW_holds E l ι a _ _ t fun j => by rw [hlam']; exact (hint j).1) hact U hOf
  let Q : MvPolynomial ((J ⊕ W × ℤ) ⊕ Z) ℤ := ∏ z : Z, MvPolynomial.X (Sum.inr z)
  have hQ : ∀ U', IsAutRepU U' → (∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ) →
      (MvPolynomial.aeval (fun j => ι.symm (η U' j)) Q ≠ 0 ↔ ∀ z ∈ Z, UpperTheory.Gal.Gen.GenAt z Φ U') := by
    intro U' g1 g2
    simp only [Q, map_prod, MvPolynomial.aeval_X, Finset.prod_ne_zero_iff, Finset.mem_univ, true_imp_iff, Subtype.forall]
    refine forall₂_congr fun z hz => ?_
    rw [← (hzact ⟨z, hz⟩ U' g1).2 g2, map_ne_zero_iff _ ι.symm.injective]
    show cz ⟨z, hz⟩ * ez ⟨z, hz⟩ U' ≠ 0 ↔ _
    simp [hcz0]
  obtain ⟨τ₀, hτ₀⟩ := exists_overPl ι v' hv'
  have hKv : ∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' a → x ∈ K := fun x hx h => (hKs v' hsv hap x hx).2 (hKwv ▸ h)
  have h2 := combine_holds (Qbar l) _ _ _ _ Q h1 (by
    rintro _ ⟨U₁, g1, g2, rfl⟩
    exact ⟨(hQ U₁ g1.aut g1.fix).2 g2, H E l ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam _ t η hint
      (fun j g hg => by
        obtain ⟨w, k1, k2, k3⟩ := hsupp j
        exact ⟨hone k1 g (k3 g hg), hone k2 g (k3 g hg)⟩) hact τ₀ hτ₀ U₁ g1⟩)
  have h3 := restrict_holds (Qbar l) _ _ Sum.inl _ _ h2
  have hval : ∀ U' : Submodule ℂ (UA E a → ℂ), (fun j => ι.symm (η U' j)) ∘ Sum.inl = Sum.elim (fun j => ι.symm (ej j U'))
      fun p : W × ℤ => ι.symm ((if h : p.1.1 ∈ W then cp (⟨p.1.1, h⟩, p.2) else 1) * PowSatU U' p.1 p.2) := fun U' => by
    funext j
    rcases j with j | p
    · rfl
    · simp only [Function.comp, η, Sum.elim_inl, Sum.elim_inr, dif_pos p.1.2]
  rw [hval] at h3
  refine h3.mono ?_
  rintro _ ⟨_, ⟨⟨U', mu, g1, g2, g3, g4, rfl⟩, hq⟩, rfl⟩
  obtain ⟨φ, hφ, hφ0, hφK⟩ := g3.fix
  have hfix' : ∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ := ⟨φ, hφ, hφ0, fun x hx => hφK x hx.1⟩
  have huniq : ∀ {V : Submodule ℂ (UA E a → ℂ)}, IsAutRepU V → ∀ {τ x y}, HasWeightAt V τ x → HasWeightAt V τ y → x = y :=
    fun hV _ _ _ hx hy => hasWeightAt_unique ⟨_, hV⟩ _ hx hy
  have hsame : SameWtOff ι w₀ v' U U' := fun τ hτ x => by
    have e : mu τ = lam τ := by
      by_contra hne
      obtain ⟨u, k1, k2⟩ := exists_of_overPair ι (g1 τ hne)
      exact k2 (hτ u k1).2
    exact ⟨fun h => by rw [huniq hU.1 h (hlam τ), ← e]; exact g3.wt τ, fun h => by rw [huniq g3.aut h (g3.wt τ), e]; exact hlam τ⟩
  refine ⟨U', _, ⟨g3.aut, fun w hw hT => ⟨φ, hφ, hφ0, fun x hx h => hφK x (hns w hw hT x hx h)⟩⟩, hlev U' g3.aut hfix',
    exists_satU g3.aut hsv ⟨φ, hφ, hφ0, fun x hx h => hφK x (hKv x hx h)⟩, hsame,
    ⟨hsame, τ₀, hτ₀, fun x hx => by rw [huniq g3.aut hx (g3.wt τ₀)]; exact g2⟩, g4, fun z hz B hB α hα => ?_,
    hsys U' g3.aut hfix', hval U'⟩
  obtain ⟨σ, hσ, hB⟩ := hB
  have := (hQ U' g3.aut hfix').1 hq z hz α ⟨σ, hσ, hα ▸ hB⟩
  rw [MvPolynomial.eval_map] at this
  rw [MvPolynomial.aeval_def]
  exact this

theorem CongUWG.congUW4 {Ty : UnitaryAutomorphicTypeClass} {Gen : ℕ → ℕ → Multiset ℂˣ → Prop} {Wt : SeedWtU} (h : CongUWG Ty Gen Wt)
    (Rk : ℕ → Prop) : CongUW4 Rk Ty Gen Wt := by
  classical
  intro E _ _ _ l _ ι a ha _ T hT U hU w₀ v' h1 h2 h3 h4 h5
  obtain ⟨Kw, g1, g2, g3, g4⟩ := h E l ι a ha T hT U hU w₀ v' h1 h2 h3 h4 h5
  refine ⟨Kw, g1, g2, g3, fun Z W hZ hW => ?_⟩
  obtain ⟨c, hc, g5⟩ := g4 (Z ∪ W) W (fun z hz => (Finset.mem_union.1 hz).elim (hZ z) fun hw => ⟨(hW z hw).1, (hW z hw).2.2⟩)
    fun w hw => ⟨(hW w hw).1, (hW w hw).2.2⟩
  refine ⟨c, hc, fun J O θ hθ => ⟨(g5 J O θ hθ).1.mono ?_, (g5 J O θ hθ).2⟩⟩
  rintro _ ⟨U', θ', k1, k2, k3, k4, k5, k6, k7, k8⟩
  exact ⟨U', θ', k1, k2, k3, k4, k5, k6, fun z hz => k7 z (Finset.mem_union_left _ hz),
    fun z hz => k7 z (Finset.mem_union_right _ hz), k8⟩

end UpperTheory.Gal.Int.Cong

end
