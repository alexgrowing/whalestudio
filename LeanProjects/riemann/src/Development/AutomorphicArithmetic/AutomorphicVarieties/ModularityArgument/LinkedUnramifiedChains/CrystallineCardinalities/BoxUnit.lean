import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.SelLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.LiftOfBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.RankTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ConjVal

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)}

private theorem adicCont_comp_ringHom_of_map_le {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [CommRing R'] (f : R →+* R')
    {I : Ideal R} {J : Ideal R'} (hIJ : I.map f ≤ J) {a : Γ → R} (ha : AdicCont I a) :
    AdicCont J (fun g => f (a g)) := by
  intro N
  have h : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hIJ N
  have := (ha N).comp (Ideal.quotientMap (J ^ N) f h)
  convert this using 1
  funext g
  simp [Ideal.quotientMap_mk]

private theorem lift_pt (S : Space O F 3) (ξ : S.R →ₐ[O] O) : UpperTheory.V.Fr.IsLift O (S.ρ.map (ξ : S.R →+* O)) := by
  have hres : (res O O : O →+* ResidueField O).comp (ξ : S.R →+* O) = (res O S.R : S.R →+* ResidueField O) :=
    RingHom.ext fun x => res_map ξ x
  have hm : (maximalIdeal S.R).map (ξ : S.R →+* O) ≤ maximalIdeal O := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← res_eq_zero_iff O O]
    have := (res_eq_zero_iff O S.R x).2 hx
    simpa [res_map] using this
  obtain ⟨hc, hb, hd⟩ := S.lift
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ?_, ?_⟩
  · exact adicCont_comp_ringHom_of_map_le _ hm (hc.1 i j)
  · exact adicCont_comp_ringHom_of_map_le _ hm (hc.2 v i)
  · rw [NRep.map_map, hres]
    exact hb
  · rw [NRep.map_map, hres]
    exact hd

private theorem box_pt {C₀ : ℕ} (hF : F.Ok C₀) (S : Space O F 3) (ξ : S.R →ₐ[O] O) :
    ∃ B : Box F 3 O, B.Of (S.ρ.map (ξ : S.R →+* O)) ∧ B.Cont (maximalIdeal O) := by
  have e : NRep.map ((ξ : S.R →+* O).comp (S.A.val : S.A →+* S.R)) S.u = S.ρ.map (ξ : S.R →+* O) := by
    apply NRep.ext
    · rfl
    · funext v i
      ext g
      rfl
  refine pr_box hF O (maximalIdeal O) _ (lift_pt S ξ).1 fun v => ?_
  rw [← e]
  exact flag hF (Or.inr rfl) S O _ v

private theorem box_unit [Algebra ℤ_[l] O] {ρ : NRep F 3 O} {B₀ : Box F 3 O} (h : B₀.Of ρ)
    (hc : B₀.Cont (maximalIdeal O)) (v : F.V) (i : Fin 2) (hu : UnitAt ρ v i) :
    ∃ B : Box F 3 O, B.Of ρ ∧ B.Cont (maximalIdeal O) ∧
      UnitStep (F.Iv v) (F.eps.comp (F.loc v)) (triOf B v) i := by
  classical
  obtain ⟨g, t, ht, hup, hdiag, hstep⟩ := hu
  have hr : ∀ s : F.Gv v, (B₀.r ((F.loc v) s)).mat = ρ.r ((F.loc0 v) s) := fun s => h.res ((F.loc0 v) s)
  let B : Box F 3 O :=
    { r := B₀.r
      nu := B₀.nu
      g := Function.update B₀.g v g
      tri := by
        intro w s
        by_cases hw : w = v
        · subst hw
          rw [Function.update_self, hr s, ← ht s]
          exact hup s
        · rw [Function.update_of_ne hw]
          exact B₀.tri w s }
  have hBg : B.g v = g := by
    show Function.update B₀.g v g v = g
    exact Function.update_self _ _ _
  have hBw : ∀ w, w ≠ v → B.g w = B₀.g w := fun w hw => by
    show Function.update B₀.g v g w = B₀.g w
    exact Function.update_of_ne hw _ _
  have htri : triOf B v = t := by
    ext s : 1
    apply Units.ext
    show (B.g v : Matrix (Fin 3) (Fin 3) O) * (B₀.r ((F.loc v) s)).mat * ((B.g v)⁻¹ : GL (Fin 3) O) = _
    rw [hBg, hr s, ht s]
  refine ⟨B, ⟨h.atc, h.res, fun w j s => ?_⟩, hc, ?_⟩
  · by_cases hw : w = v
    · subst hw
      show ((B.g w : Matrix (Fin 3) (Fin 3) O) * ρ.r ((F.loc0 w) s) * ((B.g w)⁻¹ : GL (Fin 3) O)) j j = _
      rw [hBg, ← ht s]
      exact hdiag s j
    · show ((B.g w : Matrix (Fin 3) (Fin 3) O) * ρ.r ((F.loc0 w) s) * ((B.g w)⁻¹ : GL (Fin 3) O)) j j = _
      rw [hBw w hw]
      exact h.psi w j s
  · rw [htri]
    exact hstep

private theorem zn_ext {C₀ : ℕ} (hF : F.Ok C₀) (B : Box F 3 O) (k : ℕ) {z z' : F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)}
    (hz : z ∈ ZN B k) (hz' : z' ∈ ZN B k)
    (h : ∀ s : F.G0, z s * ((boxK B k).r s).mat = z' s * ((boxK B k).r s).mat) : z = z' := by
  have hG : ∀ s : F.G0, z s = z' s := by
    intro s
    have hu : ((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k)) = 1 :=
      Units.mul_inv _
    calc z s = z s * (((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
          rw [hu, mul_one]
      _ = z' s * (((boxK B k).r s).mat * ((((boxK B k).r s).left⁻¹ : GL (Fin 3) (Ok l O k)) : Matrix (Fin 3) (Fin 3) (Ok l O k))) := by
          rw [← mul_assoc, h s, mul_assoc]
      _ = z' s := by rw [hu, mul_one]
  funext s
  have hc : ∀ y ∈ ZN B k, y (s * F.c) = y s := fun y hy => by
    rw [hy.1.1.2 s F.c, hy.2.1, map_zero, add_zero]
  rcases Int.units_eq_one_or (F.del s) with hs | hs
  · exact hG ⟨s, MonoidHom.mem_ker.mpr hs⟩
  · have hsc : F.del (s * F.c) = 1 := by
      rw [map_mul, hs, hF.del_c]
      rfl
    rw [← hc z hz, ← hc z' hz']
    exact hG ⟨s * F.c, MonoidHom.mem_ker.mpr hsc⟩

end

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.tan :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ cw : F.Inf → F.Γ, (∀ w, cw w * cw w = 1 ∧ F.del (cw w) = -1) → GWL { F with cw := cw } → LocE F → ∀ (S : Space O F 3) (ξ : S.R →ₐ[O] O) (v : F.V) (i : Fin 2), UnitAt (S.ρ.map (ξ : S.R →+* O)) v i → ∃ δ ∈ WDer S.ρ ξ O, ∃ δ' ∈ WDer S.ρ ξ O, LinearIndependent O ![δ, δ'] := by
  intro l _ O _ _ _ _ _ F C₀ hF hl cw hcw hGWL hL S ξ v i hu
  obtain ⟨B₀, hB₀, hc₀⟩ := box_pt hF S ξ
  obtain ⟨B, hB, hc, hstep⟩ := box_unit hB₀ hc₀ v i hu
  obtain ⟨C, hC⟩ := selLow l O F C₀ hF hl _ B (lift_pt S ξ) hB hc cw hcw hGWL hL v i hstep
  let T : Set S.R := {a | ∃ (w : F.V) (j : Fin 3) (s : F.Gv w), s ∈ F.Iv w ∧ a = ((S.ρ.ψ w j s : S.Rˣ) : S.R)}
  obtain ⟨δ, δ', hd, hdT, hd', hdT', hli⟩ := rankTwo l O S.R ξ T C hl (by
    intro k hk X hX hXf
    classical
    refine (hC k hk).2.trans (Nat.mul_le_mul_left C ?_)
    have hex : ∀ z ∈ ZN B k, ∃ δ ∈ X,
        ∀ (s : F.G0) (a b : Fin 3), δ (S.ρ.r s a b) = (z s * ((boxK B k).r s).mat) a b := by
      intro z hz
      obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := derOf l O F C₀ hF hl S ξ B hB hc k hk z hz
      refine ⟨δ, ?_, h3⟩
      rw [hX]
      refine ⟨h1, ?_⟩
      rintro a ⟨w, j, s, hs, rfl⟩
      exact h2 w j s hs
    let f : (F.Γ → Matrix (Fin 3) (Fin 3) (Ok l O k)) → (S.R →ₗ[O] Ok l O k) := fun z =>
      if hz : z ∈ ZN B k then (hex z hz).choose else 0
    refine Set.ncard_le_ncard_of_injOn f (fun z hz => ?_) (fun z hz z' hz' he => ?_) hXf
    · simp only [f, dif_pos hz]
      exact (hex z hz).choose_spec.1
    · apply zn_ext hF B k hz hz'
      intro s
      ext a b
      have h1 := (hex z hz).choose_spec.2 s a b
      have h2 := (hex z' hz').choose_spec.2 s a b
      simp only [f, dif_pos hz, dif_pos hz'] at he
      rw [← h1, ← h2, he])
  exact ⟨δ, ⟨hd, fun w j s hs => hdT _ ⟨w, j, s, hs, rfl⟩⟩, δ', ⟨hd', fun w j s hs => hdT' _ ⟨w, j, s, hs, rfl⟩⟩, hli⟩
