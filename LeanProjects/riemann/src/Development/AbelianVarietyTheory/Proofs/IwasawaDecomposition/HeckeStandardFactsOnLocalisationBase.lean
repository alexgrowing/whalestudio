import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeStdBase

theorem coeff_prod_isIntegral (m : Multiset ℂ) (hm : ∀ a ∈ m, IsIntegral ℤ a) (n : ℕ) :
    IsIntegral ℤ ((m.map fun a => X - C a).prod.coeff n) := by
  induction m using Multiset.induction_on generalizing n with
  | empty => simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]; split_ifs <;> simp [isIntegral_one, isIntegral_zero]
  | cons a m ih =>
    have ha : IsIntegral ℤ a := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, IsIntegral ℤ b := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons, coeff_mul]
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (ih hm' _)
    rw [coeff_sub, coeff_X, coeff_C]
    split_ifs <;> simp [isIntegral_one, isIntegral_zero, ha.neg, isIntegral_one.sub ha, ha]

theorem coeff_isIntegral_of_roots (Q : ℂ[X]) (hQ : Q.Monic) (c : ℕ) (h : ∀ a ∈ Q.roots, IsIntegral ℤ ((c : ℂ) * a)) (n : ℕ) :
    IsIntegral ℤ ((Q.scaleRoots (c : ℂ)).coeff n) := by
  have hs : Q = (Q.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQ (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))).symm
  have e : Q.scaleRoots (c : ℂ) = ((Q.roots.map fun a => a * (c : ℂ)).map fun a => X - C a).prod := by
    conv_lhs => rw [hs]
    clear hs
    induction Q.roots using Multiset.induction_on with
    | empty => simp
    | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots,
        Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons]
  rw [e]
  refine coeff_prod_isIntegral _ (fun b hb => ?_) n
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
  rw [mul_comm]
  exact h a ha

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

theorem mem_range_of_roots {K : Type} [Field K] {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    {l : ℕ} (hl : l.Prime) (hu : ∀ d : ℕ, ¬ l ∣ d → IsUnit (d : O))
    (φ : K →+* ℂ) (ψ : K →+* FractionRing O) (p : K[X]) (hp : p.Monic)
    (hr : ∀ ρ : ℂ, (p.map φ).IsRoot ρ → ∃ d : ℕ, ¬ l ∣ d ∧ IsIntegral ℤ ((d : ℂ) * ρ))
    (μ : FractionRing O) (hμ : (p.map ψ).IsRoot μ) : μ ∈ (algebraMap O (FractionRing O)).range := by
  classical
  set Q := p.map φ with hQ
  have hQm : Q.Monic := hp.map φ
  let df : ℂ → ℕ := fun ρ => if h : Q.IsRoot ρ then (hr ρ h).choose else 1
  have hdf : ∀ ρ, ¬ l ∣ df ρ := by
    intro ρ
    simp only [df]
    split_ifs with h
    · exact (hr ρ h).choose_spec.1
    · exact Nat.Prime.not_dvd_one hl
  let c : ℕ := ∏ ρ ∈ Q.roots.toFinset, df ρ
  have hc : ¬ l ∣ c := by
    intro h
    obtain ⟨ρ, -, hρ⟩ := (Prime.dvd_finset_prod_iff hl.prime _).1 h
    exact hdf ρ hρ
  have hcr : ∀ a ∈ Q.roots, IsIntegral ℤ ((c : ℂ) * a) := by
    intro a ha
    have hroot : Q.IsRoot a := (mem_roots hQm.ne_zero).1 ha
    have hd : df a ∣ c := Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.2 ha)
    obtain ⟨e, he⟩ := hd
    have h1 : IsIntegral ℤ ((df a : ℂ) * a) := by
      simp only [df, dif_pos hroot]
      exact (hr a hroot).choose_spec.2
    have : (c : ℂ) * a = (e : ℂ) * ((df a : ℂ) * a) := by
      rw [show c = df a * e from he]; push_cast; ring
    rw [this]
    have he' : IsIntegral ℤ (e : ℂ) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (e : ℤ)))
    exact IsIntegral.mul he' h1

  have hK : ∀ n, IsIntegral ℤ ((p.scaleRoots (c : K)).coeff n) := by
    intro n
    have h1 := coeff_isIntegral_of_roots Q hQm c hcr n
    have e : (p.scaleRoots (c : K)).map φ = Q.scaleRoots (c : ℂ) := by
      rw [map_scaleRoots _ _ _ (by rw [hp.leadingCoeff, map_one]; exact one_ne_zero), map_natCast]
    rw [← e, coeff_map] at h1
    exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 h1
  have hO : ∀ n, ((p.scaleRoots (c : K)).map ψ).coeff n ∈ Set.range (algebraMap O (FractionRing O)) := by
    intro n
    rw [coeff_map]
    have h3 : IsIntegral O (ψ ((p.scaleRoots (c : K)).coeff n)) := by
      obtain ⟨q, hq, he⟩ := hK n
      refine ⟨q.map (Int.castRingHom O), hq.map _, ?_⟩
      rw [eval₂_map]
      have ec : (algebraMap O (FractionRing O)).comp (Int.castRingHom O) = ψ.comp (algebraMap ℤ K) := RingHom.ext_int _ _
      rw [ec, ← hom_eval₂, he, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 h3
  have hmon : ((p.scaleRoots (c : K)).map ψ).Monic := by
    refine Monic.map ψ ?_
    rw [Monic, leadingCoeff_scaleRoots, hp.leadingCoeff]
  obtain ⟨P0, hP0, -, hP0m⟩ := lifts_and_degree_eq_and_monic ((lifts_iff_coeff_lifts _).2 hO) hmon
  have hroot : eval₂ ψ (ψ (c : K) * μ) (p.scaleRoots (c : K)) = 0 := by
    refine scaleRoots_eval₂_eq_zero ψ ?_
    rw [eval₂_eq_eval_map]; exact hμ
  have hint : IsIntegral O (ψ (c : K) * μ) := by
    refine ⟨P0, hP0m, ?_⟩
    rw [eval₂_eq_eval_map, hP0, ← eval₂_eq_eval_map]
    rw [eval₂_eq_eval_map, ← eval₂_eq_eval_map (f := ψ)] at *
    exact hroot
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  obtain ⟨u, hu'⟩ := hu c hc
  refine ⟨(↑u⁻¹ : O) * z, ?_⟩
  rw [map_mul, hz, map_natCast, ← mul_assoc, ← map_natCast (algebraMap O (FractionRing O)) c, ← hu', ← map_mul,
    Units.inv_mul, map_one, one_mul]

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

theorem exists_complexify {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [Module.Finite K E]
    {F : Type} [AddCommGroup F] [Module ℂ F] [Module.Finite ℂ F] (φ : K →+* ℂ) (j : E →ₛₗ[φ] F)
    (hj : LinearIndependent ℂ (fun i => j (Module.Free.chooseBasis K E i)) ∧
      Submodule.span ℂ (Set.range fun i => j (Module.Free.chooseBasis K E i)) = ⊤)
    (T : Module.End K E) :
    ∃ (TC : Module.End ℂ F) (b' : Module.Basis (Module.Free.ChooseBasisIndex K E) ℂ F),
      (∀ i, b' i = j (Module.Free.chooseBasis K E i)) ∧ (∀ x, TC (j x) = j (T x)) ∧ TC.charpoly = T.charpoly.map φ := by
  classical
  set b := Module.Free.chooseBasis K E with hb
  let b' : Module.Basis (Module.Free.ChooseBasisIndex K E) ℂ F := Module.Basis.mk hj.1 hj.2.ge
  have hb' : ∀ i, b' i = j (b i) := fun i => Module.Basis.mk_apply _ _ _
  let TC : Module.End ℂ F := b'.constr ℂ (fun i => j (T (b i)))
  have hcomm : ∀ x, TC (j x) = j (T x) := by
    have e : (TC.comp j : E →ₛₗ[φ] F) = j.comp T := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply, TC, ← hb', Module.Basis.constr_basis]
    intro x
    exact congrArg (fun f : E →ₛₗ[φ] F => f x) e
  have hrepr : ∀ z i, b'.repr (j z) i = φ (b.repr z i) := by
    intro z i
    have e : j z = ∑ i, φ (b.repr z i) • b' i := by
      conv_lhs => rw [← b.sum_repr z]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, hb']
    rw [e, b'.repr_sum_self]
  refine ⟨TC, b', hb', hcomm, ?_⟩
  rw [← LinearMap.charpoly_toMatrix TC b', ← LinearMap.charpoly_toMatrix T b, ← Matrix.charpoly_map]
  congr 1
  ext i k
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', hcomm, hrepr]

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

set_option synthInstance.maxHeartbeats 400000 in

theorem isRoot_of_eig (B : LocBase0 H what₂) (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ)
    [Module.Finite what₂.LL (what₂.MtL (what₂.muTw w) j)] (μ : FractionRing (B.Oc j w))
    (hμ : (B.hK j w v k).maxGenEigenspace μ ≠ ⊥) :
    ((B.hL j w v k).charpoly.map (B.ec j w)).IsRoot μ := by
  have hE : (B.hK j w v k).HasEigenvalue μ :=
    (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)).1 hμ
  obtain ⟨x, hx⟩ := hE.exists_hasEigenvector
  have hpow : ∀ (n : ℕ) (y : what₂.MtL (what₂.muTw w) j), (B.hK j w v k ^ n) (B.iV j w y) = B.iV j w ((B.hL j w v k ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, B.hK_def, ih, pow_succ, Module.End.mul_apply]
  have e : ∀ (q : Polynomial what₂.LL) (y : what₂.MtL (what₂.muTw w) j),
      Polynomial.aeval (B.hK j w v k) (q.map (B.ec j w)) (B.iV j w y) = B.iV j w (Polynomial.aeval (B.hL j w v k) q y) := by
    intro q y
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq]
    | monomial n a =>
      simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      rw [hpow, LinearMap.map_smulₛₗ]
  have hz : Polynomial.aeval (B.hK j w v k) ((B.hL j w v k).charpoly.map (B.ec j w)) = 0 := by
    have hb := (B.iV_basis j w (Module.Free.chooseBasis what₂.LL _)).2
    refine LinearMap.ext_on_range hb fun a => ?_
    rw [e, LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
  have h0 := Module.End.aeval_apply_of_hasEigenvector (p := (B.hL j w v k).charpoly.map (B.ec j w)) hx
  rw [hz, LinearMap.zero_apply] at h0
  exact (smul_eq_zero.1 h0.symm).resolve_right hx.2

end Gen

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

theorem finite_MtL {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) : Module.Finite what₂.LL (what₂.MtL μ j) := by
  have h := (what₂.jMt_basis μ j (Module.Free.chooseBasis what₂.LL _)).1
  haveI : Finite (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL μ j)) := h.finite
  exact Module.Finite.of_basis (Module.Free.chooseBasis what₂.LL _)

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in

theorem root_int (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (hP : HeckeStdPlain) (hG : GenHyp M C.Q)
    (hsp : ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ)
    (j : ℕ) (w : D.what₂.places.Pl) (v : PlE D.host) (k : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hg : GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k) (ρ : ℂ)
    (hρ : (@LinearMap.charpoly D.what₂.LL _ _ _ _ (Module.Free.of_divisionRing _ _) (finite_MtL D.what₂ _ j)
      (hLC (mt0 M) C.Q hR j w v k)).map D.what₂.embLL |>.IsRoot ρ) :
    ∃ d : ℕ, ¬ D.what₂.places.resChar w ∣ d ∧ IsIntegral ℤ ((d : ℂ) * ρ) := by
  haveI := finite_MtL D.what₂ (D.what₂.muTw w) j
  obtain ⟨s, ϖ, hcj, hu⟩ := hsp v hg.1
  obtain ⟨Bs, hOut, hB⟩ := hG w j h1 h2
  have hsB : s.v ∉ Bs := hB v k s hg hcj
  obtain ⟨hmem, hlin, -, hint⟩ := hP D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ Bs (M (D.what₂.muTw w) j h1 h2).J_open hOut s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  obtain ⟨TC, b', hb', hcomm, hchar⟩ := exists_complexify D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j)
    (D.what₂.jMt_basis _ _ _) (hLC (mt0 M) C.Q hR j w v k)
  have hev : TC.HasEigenvalue ρ := (Module.End.hasEigenvalue_iff_isRoot_charpoly TC ρ).2 (by rw [hchar]; exact hρ)
  obtain ⟨y, hy⟩ := hev.exists_hasEigenvector
  set Mr := M (D.what₂.muTw w) j h1 h2 with hMr
  have hin : ∀ z, Mr.real z ∈ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ := fun z => by
    rw [← Mr.real_range]; exact LinearMap.mem_range_self _ _
  have h0 : NG.tN Mr.J s ϖ k (0 : GAf D.host.E D.R.nV → Mr.wt.W) = 0 := by
    have := hlin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  let G : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (GAf D.host.E D.R.nV → Mr.wt.W) :=
    { toFun := fun z => NG.tN Mr.J s ϖ k (Mr.real z)
      map_add' := fun z z' => by
        have := hlin _ (hin z) _ (hin z') 1
        rw [one_smul] at this
        rw [map_add, this, one_smul]
      map_smul' := fun c z => by
        have := hlin _ (hin z) _ (Submodule.zero_mem _) c
        rw [add_zero, h0, add_zero] at this
        rw [map_smul, this]; rfl }
  have hreal : Mr.real ∘ₗ TC = G := by
    refine b'.ext fun i => ?_
    rw [LinearMap.comp_apply, hb', hcomm]
    exact hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hcj hu _
  have hf0 : Mr.real y ≠ 0 := fun h => hy.2 (Mr.real_inj (by rw [h, map_zero]))
  have hfe : NG.tN Mr.J s ϖ k (Mr.real y) = ρ • Mr.real y := by
    have e := congrArg (fun f => f y) hreal
    simp only [LinearMap.comp_apply] at e
    rw [hy.apply_eq_smul, map_smul] at e
    exact e.symm
  have hnab : ¬ s.Above (D.what₂.places.resChar w) := by
    intro hab
    have hw : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := by
      have := hab
      unfold SplitPlace.Above at this
      rw [← s.w_under, Ideal.mem_comap, map_natCast] at this
      exact this
    apply hg.2.1
    show ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
    exact (hcj _ _ (by simp)).2 hw
  exact hint _ (hin y) hf0 ρ hfe _ (D.what₂.places.resChar_prime w) hnab

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

set_option synthInstance.maxHeartbeats 400000 in

theorem heckeStd0_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂)
    (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → GenHyp M C.Q →
    (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) →
    (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) →
    HeckeStd0 (base M C hR X hS) := by
  intro D M C hR X hS hP hG hsp hc j w h1 h2
  refine ⟨fun v k v' k' _ _ => ?_, fun v k hg μ hμ => ?_⟩
  · have hb := (iVC_basis X j w (Module.Free.chooseBasis D.what₂.LL _)).2
    refine LinearMap.ext_on_range hb fun a => ?_
    change (base M C hR X hS).hK j w v k ((base M C hR X hS).hK j w v' k' ((base M C hR X hS).iV j w _)) =
      (base M C hR X hS).hK j w v' k' ((base M C hR X hS).hK j w v k ((base M C hR X hS).iV j w _))
    rw [(base M C hR X hS).hK_def, (base M C hR X hS).hK_def, (base M C hR X hS).hK_def, (base M C hR X hS).hK_def,
      ← Module.End.mul_apply, ← Module.End.mul_apply]
    exact congrArg (fun f : Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) =>
      (base M C hR X hS).iV j w (f ((Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) a))) (hc j w v k v' k').eq
  haveI := finite_MtL D.what₂ (D.what₂.muTw w) j
  have hroot := isRoot_of_eig (base M C hR X hS) j w v k μ hμ
  have hu : ∀ d : ℕ, ¬ D.what₂.places.resChar w ∣ d → IsUnit (d : OcC X j w) := by
    intro d hd
    have h : IsUnit (d : ℤ_[D.what₂.places.resChar w]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd (D.what₂.places.resChar_prime w)).2 hd
    simpa using h.map (algebraMap ℤ_[D.what₂.places.resChar w] (OcC X j w))
  exact mem_range_of_roots (D.what₂.places.resChar_prime w) hu D.what₂.embLL (ecC X j w) _ (LinearMap.charpoly_monic _)
    (fun ρ hρ => root_int M C hR hP hG hsp j w v k h1 h2 hg ρ hρ) μ hroot

end GlobalTheory.HeckeStdBase
