import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SemisimpleOfFin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal

noncomputable section

namespace UpperTheory.GalS

open Formalism.MainNotions.SumRepresentations Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal Topology

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))

private theorem exists_isCompl_finrank_inertia_of_charpoly (A : NAut N) (hr : GoodR N i r) (hTY : At.MonodromyInertiaType N A)
    (w : PlE H) (hS : w ∈ N.S i) (hg : ∃ k, w ∈ placesOver H.E (H.g k)) (hL : LGCatN N r A w)
    (hmult : ∀ x, rootMultiplicity (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))
      (((redRep N i (r x) (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) _).charpoly) = R.t)
    (x : N.X i) :
    ∃ U U' : Submodule (Qbar (N.l i)) (Fin R.nV → Qbar (N.l i)), IsCompl U U' ∧
      Module.finrank (Qbar (N.l i)) U' = R.t ∧
      ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        (∀ v ∈ U, ((mapRep (iotaOQ N A i) (r x) γ : GL _ _) :
            Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))).mulVec v ∈ U) ∧
        ∀ v ∈ U', ((mapRep (iotaOQ N A i) (r x) γ : GL _ _) :
            Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))).mulVec v = iotaOQ N A i (chi1 N i γ) • v := by
  have hw : w ∉ placesOver H.E (N.l i) := N.SQ_l i w (Or.inl hS)
  have hcont : Continuous fun g => ((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
    contQ_of_continuous N A i (r x) (hr x).1
  obtain ⟨P, -, hP0⟩ := hL x
  obtain ⟨s, hP⟩ : ∃ s : ℝ, RelU N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w)
      (A.lpTw (A.locV i P w) s) := ⟨_, hP0⟩
  have hγ₀I : N.gam0 i w ∈ Ine (F := H.E) (N.plOm.1 w) := N.locNd_chebotarevPlace_mem i w
  have htame := (N.restN_tameGenerator_generates i w (Or.inl hS)).2
  have hcpQ : ∀ g, (((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly =
      (((r x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))).charpoly.map (iotaOQ N A i) :=
    fun g => Matrix.charpoly_map _ _
  have hle : rootMultiplicity (iotaOQ N A i (chi1 N i (N.gam0 i w)))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly ≤ R.t := by
    rw [hcpQ, ← hmult x]
    refine (rootMult_le_of_maps (iotaOQ N A i) (iotaOQ_injective N A i)
      (IsLocalRing.residue (N.O i)) _ (Matrix.charpoly_monic _) _).trans (le_of_eq ?_)
    rw [← Matrix.charpoly_map]
    rfl
  have hine : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly.map (A.iotaQC i).toRingHom =
        A.inePol (A.locV i P w) σ := fun σ hσ =>
    ((A.wdOf_ine i _ w hw hcont σ hσ).trans (hP.ine σ hσ)).trans (A.inePol_tw _ s σ hσ)
  have hdim : A.lpDim (A.locV i P w) = R.nV := by
    rw [← A.lpDim_tw _ s, ← hP.dim, A.wdOf_dim]
  have hne : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locV i P w) σ ≠ 0 := by
    intro σ hσ
    rw [← hine σ hσ]
    exact ((Matrix.charpoly_monic _).map _).ne_zero
  have hleC : rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w)))
      (A.inePol (A.locV i P w) (N.gam0 i w)) ≤ R.t := by
    rw [← hine _ hγ₀I]
    exact (eq_rootMultiplicity_map (A.iotaQC i).injective _).symm.trans_le hle
  obtain ⟨a, b, hab, -, -, -, hb⟩ := hTY.2.1 i P w hS hg htame hleC
  have hdivC : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (X - C (iotaO N A i (chi1 N i σ))) ^ R.t ∣ A.inePol (A.locV i P w) σ := by
    intro σ hσ
    rw [hab, A.inePol_sum, hb σ hσ]
    exact dvd_mul_left _ _
  have hge : R.t ≤ rootMultiplicity (iotaOQ N A i (chi1 N i (N.gam0 i w)))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly := by
    have h1 := (le_rootMultiplicity_iff (hne _ hγ₀I)).mpr (hdivC _ hγ₀I)
    rw [← hine _ hγ₀I] at h1
    exact h1.trans_eq (eq_rootMultiplicity_map (A.iotaQC i).injective _).symm
  have hinj : Function.Injective (Polynomial.map (R := Qbar (N.l i)) (A.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC i).injective
  have ht0 : R.t ≠ 0 := fun h => by
    have := R.t_odd
    rw [h] at this
    exact (Nat.not_odd_zero this)
  have hiO : Function.Injective (iotaO N A i) := fun a b h =>
    iotaOQ_injective N A i ((A.iotaQC i).injective h)
  obtain ⟨χ, hχ⟩ : ∃ χ : G H.E N.Om →* (Qbar (N.l i))ˣ,
      χ = (Units.map (iotaOQ N A i).toMonoidHom).comp (N.chi i 1) := ⟨_, rfl⟩
  have hχv : ∀ g, ((χ g : (Qbar (N.l i))ˣ) : Qbar (N.l i)) = iotaOQ N A i (chi1 N i g) := by
    intro g
    rw [hχ]
    rfl
  have hχcont : Continuous fun g => ((χ g : (Qbar (N.l i))ˣ) : Qbar (N.l i)) := by
    simp only [hχv]
    exact (continuous_iotaOQ N A i).comp (N.chi_cont i 1)
  have hfin := (A.wdOf_mono0 i _ w hw hcont).mp hP.mono
  have hfo : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), IsOfFinOrder (mapRep (iotaOQ N A i) (r x) σ) := by
    intro σ hσ
    refine finite_zpowers.mp (hfin.subset ?_)
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨σ ^ k, Subgroup.zpow_mem _ hσ k, map_zpow _ σ k⟩
  have hwild : ∀ σ ∈ wildSet N (N.plOm.1 w), σ ∈ Ine (F := H.E) (N.plOm.1 w) ∧
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly = (X - 1) ^ R.nV ∧ χ σ = 1 := by
    intro σ hσ
    have hσI : σ ∈ Ine (F := H.E) (N.plOm.1 w) := GlobalTheory.TameEig.wild_mem_Ine (N.plOm.1 w) σ hσ
    have hX : A.inePol (A.locV i P w) σ = (X - 1) ^ R.nV := by
      rw [← A.inePol_tw _ s σ hσI, hP.nice.1 σ hσI hσ, A.lpDim_tw, hdim]
    refine ⟨hσI, ?_, ?_⟩
    · apply hinj
      rw [hine σ hσI, hX]
      simp
    · have h1 := hdivC σ hσI
      rw [hX, show (X - 1 : Polynomial ℂ) = X - C 1 by simp] at h1
      have h2 := (Polynomial.prime_X_sub_C (iotaO N A i (chi1 N i σ))).dvd_of_dvd_pow
        ((dvd_pow_self _ ht0).trans h1)
      have h3 := Polynomial.dvd_iff_isRoot.mp h2
      rw [Polynomial.root_X_sub_C] at h3
      have h4 : chi1 N i σ = 1 := hiO (by rw [← h3, map_one])
      ext
      rw [hχv, h4, map_one]
      rfl
  have hm : rootMultiplicity ((χ (N.gam0 i w) : (Qbar (N.l i))ˣ) : Qbar (N.l i))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly = R.t := by
    rw [hχv]
    exact le_antisymm hle hge
  obtain ⟨U, U', hUU, hd, hact⟩ := split_tame (Ine (F := H.E) (N.plOm.1 w))
    (wildSet N (N.plOm.1 w)) (N.gam0 i w) hγ₀I htame (mapRep (iotaOQ N A i) (r x)) hcont χ hχcont
    hfo hwild hm
  refine ⟨U, U', hUU, hd, fun γ hγ => ⟨(hact γ hγ).1, fun v hv => ?_⟩⟩
  rw [(hact γ hγ).2 v hv, hχv]

theorem exists_inertia_charpoly_factor_of_tame_type (A : NAut N) (hC : Cheb N) (hr : GoodR N i r) (hT : At.TieGal N A) (hTY : At.MonodromyInertiaType N A)
    (w : PlE H) (hS : w ∈ N.S i) (hg : ∃ k, w ∈ placesOver H.E (H.g k))
    (hL : LGCatN N r A w)
    (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) (hrb : IsRhoBar N i rb)
    (hnr : ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))) :
    ∃ Pp : Polynomial (N.T i),
      IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
      ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
            (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
          (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0 := by
  have hw : w ∉ placesOver H.E (N.l i) := N.SQ_l i w (Or.inl hS)
  exact weil_deligne_clause_of_split N r (charpoly_clause_of_chebotarev N hC i r hr) w (iotaOQ N A i) (iotaOQ_injective N A i)
    (exists_isCompl_finrank_inertia_of_charpoly N r A hr hTY w hS hg hL (mult_of_rhobar N r hC hr rb hrb w hw hnr))
    (mult_of_rhobar N r hC hr rb hrb w hw hnr)

theorem SplitI_of_TY (A : NAut N) (hr : GoodR N i r) (w : PlE H) (hw : w ∉ placesOver H.E (N.l i))
    (hL : LGCatN N r A w)
    (hty : ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t)
    (x : N.X i) : SplitI N r w x := by
  have hcont : Continuous fun g => ((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
    contQ_of_continuous N A i (r x) (hr x).1
  obtain ⟨P, -, hP0⟩ := hL x
  obtain ⟨s, hP⟩ : ∃ s : ℝ, RelU N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w)
      (A.lpTw (A.locV i P w) s) := ⟨_, hP0⟩
  have hine : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly.map (A.iotaQC i).toRingHom =
        A.inePol (A.locV i P w) σ := fun σ hσ =>
    ((A.wdOf_ine i _ w hw hcont σ hσ).trans (hP.ine σ hσ)).trans (A.inePol_tw _ s σ hσ)
  have hfin := (A.wdOf_mono0 i _ w hw hcont).mp hP.mono
  have ht0 : R.t ≠ 0 := fun h => by
    have := R.t_odd
    rw [h] at this
    exact (Nat.not_odd_zero this)
  haveI : CharZero (Kf N i) := ((A.iotaQC i).toRingHom.comp (A.iotaQ i)).charZero
  let ρ : Ine (F := H.E) (N.plOm.1 w) →* GL (Fin (R.r + R.t)) (Kf N i) :=
    (mapRep (algebraMap (N.O i) (Kf N i)) (r x)).comp (Ine (F := H.E) (N.plOm.1 w)).subtype
  let χ : Ine (F := H.E) (N.plOm.1 w) →* (Kf N i)ˣ :=
    ((Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom).comp (N.chi i 1)).comp
      (Ine (F := H.E) (N.plOm.1 w)).subtype
  have hrange : (Set.range ρ).Finite := by
    refine Set.Finite.of_finite_image (f := Units.map
      (RingHom.toMonoidHom (RingHom.mapMatrix (m := Fin (R.r + R.t)) (A.iotaQ i)))) ?_ ?_
    · refine hfin.subset ?_
      rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
      exact ⟨γ.1, γ.2, Units.ext rfl⟩
    · intro u _ v _ h
      apply Units.ext
      have h' := congrArg (fun z : GL (Fin (R.r + R.t)) (Qbar (N.l i)) =>
        (z : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l i)))) h
      exact Matrix.map_injective (A.iotaQ i).injective h'
  have hcp : ∀ γ, ((ρ γ : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Kf N i)).charpoly =
      (X - 1) ^ R.r * (X - C ((χ γ : (Kf N i)ˣ) : Kf N i)) ^ R.t := by
    intro γ
    apply Polynomial.map_injective ((A.iotaQC i).toRingHom.comp (A.iotaQ i))
      ((A.iotaQC i).toRingHom.comp (A.iotaQ i)).injective
    have hmat : ((ρ γ : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Kf N i)).map (A.iotaQ i) =
        ((mapRep (iotaOQ N A i) (r x) γ.1 : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
      rfl
    rw [← Polynomial.map_map, ← Matrix.charpoly_map, hmat]
    refine (hine γ.1 γ.2).trans ?_
    rw [(hty P).2 γ.1 γ.2]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C]
    rfl
  obtain ⟨Pm, hPm⟩ := split_of_charpoly ht0 ρ χ hrange hcp
  exact ⟨Pm, fun γ hγ => hPm ⟨γ, hγ⟩⟩

end UpperTheory.GalS
