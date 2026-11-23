import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.UnitCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymOfVieta

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem unit_card (l : ℕ) [hl : Fact l.Prime] (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] :
    IsUnit (resCard (w.adicCompletion L) : O) := by
  rw [resCard_eq_normV]
  by_contra hn
  have h1 : residue O (normV w : O) = 0 := (residue_eq_zero_iff _).2 hn
  rw [map_natCast, CharP.cast_eq_zero_iff (ResidueField O) l] at h1
  have hmax := w.isMaximal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 L ⧸ w.asIdeal)
  have h2 : l ∣ Fintype.card (𝓞 L ⧸ w.asIdeal) := by
    rw [← Nat.card_eq_fintype_card]; exact h1
  have h3 := (prime_dvd_char_iff_dvd_card (R := 𝓞 L ⧸ w.asIdeal) l).2 h2
  have h4 : ringChar (𝓞 L ⧸ w.asIdeal) = l :=
    ((Nat.prime_dvd_prime_iff_eq hl.out (CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) _)).1 h3).symm
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← h4]
  exact ringChar.Nat.cast_ringChar
private theorem chi_monic {n : ℕ} {A G : Type} [CommRing A] [Nontrivial A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) :
    (D.chi y).Monic ∧ (D.chi y).natDegree = n := by
  obtain ⟨h0, -, -, -, h1, h2, -⟩ := UpperTheory.V.CA.d_chi D.toDet y
  rw [Det.lam, pow_zero, one_mul, Nat.sub_zero] at h0
  rw [(UpperTheory.V.CA.d_toDet D y).1] at h0 h1 h2
  exact ⟨h1, le_antisymm h2 (Polynomial.le_natDegree_of_ne_zero (by rw [h0]; exact one_ne_zero))⟩
private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  rw [GDet.lam, GDet.lam, this]
private theorem lam_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G) (f : A →+* A')
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
private theorem fix_le {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) :
    fixd ρ (UK n w) ≤ fixd ρ (UC n w fun _ => ⊤) := by
  intro m hm u hu
  refine hm u fun j _ => ?_
  have h1 : iwC ((w j).adicCompletion L) n ⊤ ≤ KO _ (Fin n) := by
    rw [(memIwC _ n ⊤).2.1]
    exact iwahori_le_KO _ (Fin n)
  exact h1 (hu j trivial)
private theorem fix_at {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (j : Fin q) :
    fixd ρ (UK n w) ≤ fixd (ρ.comp (atJ n w j)) (KO _ (Fin n)) := by
  intro m hm u hu
  refine hm (atJ n w j u) fun j' _ => ?_
  by_cases e : j' = j
  · subst e
    simpa [atJ] using hu
  · simp [atJ, Pi.mulSingle_eq_of_ne e]
private theorem two_gen (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (O A B M N : Type)
    [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (ρ : Representation A (GV n w) M) (β : A →+* B) (P : Fin q → Polynomial B)
    (act : PU A q n →ₐ[A] Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (H : HkHyp O (qj w) act e
      (fun j => (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype))
    (he : ∀ v, ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w))
    (eM : fixd ρ (UK n w) ≃+ N) (hM : ∀ (t : A) m, eM (t • m) = β t • eM m)
    (hP : ∀ j, (P j).Monic ∧ (P j).natDegree = n) (c : Fin q → ℕ → A)
    (hc : ∀ j k, β (c j k) = (-1) ^ k * (P j).coeff (n - k))
    (hs : ∀ j k, k ≤ n → ∀ m : fixd ρ (UC n w fun _ => ⊤), (m : M) ∈ fixd ρ (UK n w) →
      act (emb ℤ A j (MvPolynomial.esymm (Fin n) ℤ k)) m = c j k • m) :
    TwoMaps (M := N) β P act (fEl (qj w) fun j i => MvPolynomial.X (j, i)) := by
  let inc : N →+ fixd ρ (UC n w fun _ => ⊤) :=
    (Submodule.inclusion (fix_le ρ)).toAddMonoidHom.comp eM.symm.toAddMonoidHom
  have hinc : ∀ m, (inc m : M) = eM.symm m := fun _ => rfl
  let t0 : fixd ρ (UC n w fun _ => ⊤) →ₗ[A] fixd ρ (UK n w) :=
    ((fixd ρ (UC n w fun _ => ⊤)).subtype.comp (List.ofFn e).prod).codRestrict _ he
  let tr : fixd ρ (UC n w fun _ => ⊤) →+ N := eM.toAddMonoidHom.comp t0.toAddMonoidHom
  have hβ : ∀ (t : A) m, inc (β t • m) = t • inc m := fun t m => Subtype.ext (by
    obtain ⟨m, rfl⟩ := eM.surjective m
    rw [← hM, Submodule.coe_smul, hinc, hinc, eM.symm_apply_apply, eM.symm_apply_apply, Submodule.coe_smul])
  refine twoMul O A B N _ q n β P act (qj w) (multiTwo O A B N _ q n (qj w) β P act e _ inc tr H (fun j => (hP j).1)
    (fun j => (hP j).2) ?_ hβ (fun v => Subtype.ext ?_) (fun j m => fix_at ρ j (eM.symm m).2) fun j k hk m => ?_)
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    rw [hinc, hinc] at h1
    exact eM.symm.injective (Subtype.ext h1)
  · rw [hinc]
    exact congrArg Subtype.val (eM.symm_apply_apply (t0 v))
  · rw [hs j k hk (inc m) (eM.symm m).2, ← hc, hβ]
theorem UpperTheory.V.Pa.Lev.twoOf_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ph ta : Fin q → (globOf r V).G₀), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → TwoMaps (M := b.M) A.β.toRingHom (fun j => (pairOf B.u).D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) T.actw (fEl (qj w) fun j i => MvPolynomial.X (j, i)) := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ hl hx hδ T ph ta hok
  have hs := _root_.UpperTheory.V.Z.Win.T2.symOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ hl hx hδ T ph ta hok
  have hch : CharP (ResidueField O) l := UpperTheory.V.Pa.IsCoef.char
  obtain ⟨ι, hι, -⟩ := hok
  obtain ⟨e, H, he⟩ := hkHypOf L n q w l O A.R A.P A.ρ x δ T hx (fun j => unit_card l L (w j) (hl j) O)
    (fun k m hk hm => hι m fun y => by
      have h1 := congrArg y.sp hm
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact (smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hk))
  refine two_gen L n q w O A.R B.B A.P b.M A.ρ A.β.toRingHom _ T.actw e H he A.eM A.eM_smul
    (fun j => chi_monic _ _) (fun j k => A.p.D.lam k (MonoidAlgebra.single (ph j) 1)) (fun j k => ?_) hs
  exact (lam_map A.p.D A.β.toRingHom k (ph j)).symm.trans
    ((congrArg (fun D' => GDet.lam D' k (MonoidAlgebra.single (ph j) 1)) A.β_pair.1).trans (lam_comap _ _ k _))
end
