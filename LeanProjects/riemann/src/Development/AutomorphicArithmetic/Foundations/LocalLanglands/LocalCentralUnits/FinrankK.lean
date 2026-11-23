import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzNormV
import Development.DiscreteGroups.GlobalIrreducibility.DzTameRec
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameArt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsExists

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {g n : ℕ} [Fact g.Prime]

private theorem exists_lift (D : Ext h g n) (hn : 0 < n) (t : Ine (F := E) A) :
    ∃ t' : Ine (F := D.E') A, (t : G E Ω) = AlgEquiv.restrictScalars E (t' : G D.E' Ω) := by
  obtain ⟨s, hs, e⟩ := ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  exact ⟨⟨s, hs⟩, e.symm⟩

private theorem lift_unique (D : Ext h g n) {t : Ine (F := E) A} {s s' : Ine (F := D.E') A}
    (e : (t : G E Ω) = AlgEquiv.restrictScalars E (s : G D.E' Ω))
    (e' : (t : G E Ω) = AlgEquiv.restrictScalars E (s' : G D.E' Ω)) : s = s' :=
  Subtype.ext (AlgEquiv.restrictScalars_injective E (e.symm.trans e'))

private theorem finrank_K (D : Ext h g n) (hn : 0 < n) : Module.finrank (ZMod g) D.K = n := by
  have hgp : g.Prime := Fact.out
  have e : (𝓞 D.E' ⧸ RingHom.ker D.red) ≃+* D.K := RingHom.quotientKerEquivOfSurjective D.surj
  have hc : Nat.card D.K = g ^ n := by
    rw [← Nat.card_congr e.toEquiv, D.ker]
    exact D.card
  have : Finite D.K := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hgp.ne_zero)
  have hm := Module.natCard_eq_pow_finrank (K := ZMod g) (V := D.K)
  rw [hc, Nat.card_zmod] at hm
  exact (Nat.pow_right_injective hgp.two_le hm).symm

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
theorem UpperTheory.Zero.LLC.resEx :
    UpperTheory.Zero.LLC.ResEx := by
  intro E Ω _ _ _ _ _ A w h g _ i hi n hn D
  obtain ⟨R0, hR0⟩ := exists_resHom (h' := D.h') D.ha' (K := D.K) (red := D.red) D.ker
  have hlift := exists_lift D hn
  refine ⟨?_, fun R hR => ?_⟩
  · choose L hL using hlift
    refine ⟨MonoidHom.mk' (fun t => R0 (L t)) fun s t => ?_, ?_⟩
    · rw [← map_mul]
      congr 1
      refine lift_unique D (hL (s * t)) ?_
      rw [Subgroup.coe_mul, hL s, hL t]
      rfl
    · intro t t' x z e hx hv
      have e1 : L t = t' := lift_unique D (hL t) e
      apply Units.ext
      rw [← hx]
      show ((R0 (L t) : D.Kˣ) : D.K) = _
      rw [e1]
      exact hR0 t' x hv
  ·
    have hRR : ∀ (t : Ine (F := E) A) (t' : Ine (F := D.E') A),
        (t : G E Ω) = AlgEquiv.restrictScalars E (t' : G D.E' Ω) → R t = R0 t' := by
      intro t t' e
      obtain ⟨x, hx⟩ := exists_int_approx_compl D.w' _ (val_artin_ine D.ha' t').le
      have hne := red_ne_zero_of_approx D.ha' D.ker hx
      rw [hR t t' x (Units.mk0 _ hne) e rfl hx]
      exact Units.ext (hR0 t' x hx).symm
    have hone : ∀ t' : Ine (F := D.E') A,
        Valued.v ((D.a' (ineIncl D.h' t') : D.w'.adicCompletion D.E') - 1) < 1 → R0 t' = 1 := by
      intro t' hv
      apply Units.ext
      rw [hR0 t' 1 (by simpa using hv)]
      simp
    have hwild : ∀ t : Ine (F := E) A, Formalism.MainNotions.BlochKatoReduction.IsWild A (t : G E Ω) → R t = 1 := by
      intro t hw
      obtain ⟨t', e⟩ := hlift t
      rw [hRR t t' e]
      refine hone t' (PositivityTheory.LocalParametersCuspidal.DZC.wild_to_unitsOne D.a' D.ha' (ineIncl D.h' t') ⟨t'.2, fun x hx => ?_⟩)
      have := hw.2 x hx
      rw [e] at this
      exact this
    have hq : normV w = g := normV_eq_of_padic w g i hi
    refine ⟨hn, hq, finrank_K D hn, ?_, ?_, hwild, ?_⟩
    · intro z
      obtain ⟨t', x, hx, hv⟩ := exists_ine_of_res g A D.w' D.h' n hn D.card D.a' D.ha' D.K D.red D.surj D.ker z
      exact ⟨⟨AlgEquiv.restrictScalars E (t' : G D.E' Ω), GlobalTheory.AboveL.ResEx.res_mem_Ine t'.2⟩,
        hR _ t' x z rfl hx hv⟩
    ·
      set U : Set (D.w'.adicCompletion D.E')ˣ := {u | Valued.v ((u : D.w'.adicCompletion D.E') - 1) < 1} with hUdef
      have hU : U ∈ nhds (1 : (D.w'.adicCompletion D.E')ˣ) := by
        have h0 : {x : D.w'.adicCompletion D.E' | Valued.v (x - 1) < 1} ∈
            nhds ((1 : (D.w'.adicCompletion D.E')ˣ) : D.w'.adicCompletion D.E') := by
          rw [Valued.mem_nhds]
          exact ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
        exact Units.continuous_val.continuousAt.preimage_mem_nhds h0
      have hV : (fun τ : Ine (F := D.E') A => D.a' (ineIncl D.h' τ)) ⁻¹' U ∈ nhds (1 : Ine (F := D.E') A) := by
        refine D.ha'.cont.continuousAt.preimage_mem_nhds ?_
        simpa using hU
      obtain ⟨O, hO, hOs⟩ := (mem_nhds_induced Subtype.val (1 : Ine (F := D.E') A) _).1 hV
      rw [OneMemClass.coe_one] at hO
      obtain ⟨L, hL, hLO⟩ := (krullTopology_mem_nhds_one_iff D.E' Ω O).1 hO
      have : Module.Finite E D.E' := Module.Finite.of_restrictScalars_finite ℚ E D.E'
      have : FiniteDimensional E (L.restrictScalars E) := by
        show Module.Finite E L
        exact Module.Finite.trans D.E' L
      let H1 : Subgroup (Ine (F := E) A) :=
        (L.restrictScalars E).fixingSubgroup.comap (Ine (F := E) A).subtype
      have hH1 : IsOpen (H1 : Set (Ine (F := E) A)) :=
        (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val
      refine Subgroup.isOpen_mono (fun t ht => ?_) hH1
      obtain ⟨t', e⟩ := hlift t
      have hfix : (t' : G D.E' Ω) ∈ L.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 ht x hx
        rw [show (Ine (F := E) A).subtype t = (t : G E Ω) from rfl, e] at this
        exact this
      have hm : t' ∈ (fun τ : Ine (F := D.E') A => D.a' (ineIncl D.h' τ)) ⁻¹' U := hOs (hLO hfix)
      show R t = 1
      rw [hRR t t' e]
      exact hone t' hm
    · intro σ t t' hd hc
      have hF : IsFrob A g (σ : G E Ω) := hq ▸ deg_eq_one_iff.1 hd
      have hW := isWild_frob hF t
      have e : (⟨(σ : G E Ω) * t * (σ : G E Ω)⁻¹, conj_mem_Ine hF.1 t.2⟩ : Ine (F := E) A) = t' :=
        Subtype.ext (congrArg Subtype.val hc).symm
      rw [e] at hW
      have := hwild _ hW
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at this
      exact this

end
