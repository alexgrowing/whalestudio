import Formalism.SharpRestriction.LevelLetterCocycles.ExtDataOneMapSmulO
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem extData_win (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) (hηb : η ≤ b i) :
    Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i ⊆
      Set.Icc (-(Formalism.MainNotions.RamifiedCoefficientChains.MiW d b S η i : ℤ)) (Formalism.MainNotions.RamifiedCoefficientChains.hiW d b S η i : ℤ) := by
  intro x hx
  unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at hx
  unfold Formalism.MainNotions.RamifiedCoefficientChains.MiW Formalism.MainNotions.RamifiedCoefficientChains.hiW
  split_ifs at hx ⊢ with h <;> simp only [Set.mem_union, Set.mem_Icc] at hx ⊢ <;> push_cast at hx ⊢ <;> omega

theorem extData_lin {FF M I : Type} [AddCommGroup FF] [Module O FF] [AddCommGroup M] [Module O M] [Fintype I]
    (P : M → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : O) x, P x → P (c • x))
    (bF : Module.Basis I O FF) (Φ : FF →ₗ[O] M) (h : ∀ j, P (Φ (bF j))) (f : FF) : P (Φ f) := by
  rw [← bF.sum_equivFun f, map_sum]
  exact Finset.sum_induction _ P hadd h0 fun j _ => by rw [map_smul]; exact hsmul _ _ (h j)

theorem extData_extTool [NeZero n] (W : LocWach PD LL O v n)
    (hH : Formalism.MainNotions.ElementDenominator.coreHerrExtΔ W) (hExt : Formalism.MainNotions.LiftingTheory.liftb_HExt W) (hOne : Formalism.MainNotions.LiftingTheory.liftb_HOne W)
    (hKer : Formalism.MainNotions.LiftingTheory.liftb_HKer W) (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O)
    (hEx : ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
      IsSESLat (Qp := Qp) (O := O) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧
        ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x)
    (hdex : W.DelF.card = PD.p - 1 → ∃ d : O, d * (W.DelF.card : O) = 1)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hQ : Formalism.MainNotions.CrystallineLiftingInputs.QTool W) :
    ExtTool W := by
  intro d T₁ T₂ F b S η m hS FF _ _ _ _ g
  have hS' := hS
  obtain ⟨hA, h11, -, hOd, hζ, hSur, hJ1, -, hab, -⟩ := hS
  have hηb : ∀ i, η ≤ b i := fun i => by
    have h0 := Formalism.MainNotions.RamifiedCoefficientChains.aR_nonneg PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) (by omega)
    have h1 := hab i
    have h2 : (η : ℝ) ≤ (b i : ℝ) := by linarith
    exact_mod_cast h2
  set Mi := Formalism.MainNotions.RamifiedCoefficientChains.MiW d b S η with hMi
  set hi := Formalism.MainNotions.RamifiedCoefficientChains.hiW d b S η with hhi
  set a := ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊ with ha
  have c1 : IsCrys PD T₁.ρ := hSur.1
  have c2 : IsCrys PD T₂.ρ := hSur.2.1
  have hOc : IsCrys PD W.one.ρ := hOne.1
  have hJL1 : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi := fun i τ hτ x hx => extData_win d b S η i (hηb i) (hJ1 i τ hτ x hx)
  obtain ⟨T₀, ι₀, hses₀, c0⟩ := hKer T₁ T₂ F hSur
  have hJY : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W Y Mi hi := by
    intro Y ι π hses hY τ i hτ x hx
    rcases (hJmp T₂ Y W.one ι π hses c2 hY hOc τ x).1 hx with h | h
    · exact hJL1 i τ hτ x ((hJmp T₀ T₁ T₂ ι₀ F hses₀ c0 c1 c2 τ x).2 (Or.inr h))
    · rw [hOne.2.1 τ x h]
      simp
  have hQ1 := (hQ d T₁ T₂ F b S η m Mi hi hS' hJL1).2
  set N := eWA PD.p (Hmax n Mi hi) with hN
  have hK : ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) (O := O) ι π → IsCrys PD Y.ρ → ∀ i : ZMod n,
        Kills W π i (lp W N) ∧ Kills W π i (qp W ^ a) := fun Y ι π hses hY i =>
    ⟨(hQ1 Y ι π hses hY i).2.1, (hQ1 Y ι π hses hY i).2.2⟩

  let I := Module.Free.ChooseBasisIndex O FF
  let bF : Module.Basis I O FF := Module.Free.chooseBasis O FF
  have one := fun j : I => extDataOne_exists W hH hExt hOne hEx hdex h5 h6 h9 hA hζ hOd T₂ c2 Mi hi a N
    hJY hK (g (bF j) : G → T₂.V) (g (bF j)).2
  choose yj zj μj νj hZj hcZj hclj hRelj using one
  let y : FF →ₗ[O] W.DD T₂ := bF.constr O yj
  let z : FF →ₗ[O] W.DD T₂ := bF.constr O zj
  let μ : ZMod n → FF →ₗ[O] W.DD T₂ := fun i => bF.constr O fun j => μj j i
  let ν : ZMod n → FF →ₗ[O] W.DD T₂ := fun i => bF.constr O fun j => νj j i
  have hyb : ∀ j, y (bF j) = yj j := fun j => bF.constr_basis O yj j
  have hzb : ∀ j, z (bF j) = zj j := fun j => bF.constr_basis O zj j
  have hμb : ∀ i j, μ i (bF j) = μj j i := fun i j => bF.constr_basis O (fun j => μj j i) j
  have hνb : ∀ i j, ν i (bF j) = νj j i := fun i j => bF.constr_basis O (fun j => νj j i) j
  refine ⟨N, y, z, μ, ν, fun f => ?_, fun i f => ?_⟩
  · have hκ : ((g f : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V) ∈ latticeCocycles T₂.L := (Submodule.mem_inf.1 (g f).2).1
    have hyf : y f = ∑ j, bF.equivFun f j • yj j := by simp [y, Module.Basis.constr_apply_fintype]
    have hzf : z f = ∑ j, bF.equivFun f j • zj j := by simp [z, Module.Basis.constr_apply_fintype]
    have hpair : ((y f, z f) : W.DD T₂ × W.DD T₂) = ∑ j, bF.equivFun f j • ((yj j, zj j) : W.DD T₂ × W.DD T₂) := by
      rw [hyf, hzf]
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have hmem : ((y f, z f) : W.DD T₂ × W.DD T₂) ∈ herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂) := by
      rw [hpair]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hZj j)
    refine ⟨⟨(y f, z f), hmem⟩, hκ, rfl, ?_⟩
    have hx : (⟨(y f, z f), hmem⟩ : ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) =
        ∑ j, bF.equivFun f j • (⟨(yj j, zj j), hZj j⟩ :
          ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hpair
    have hsum : (⟨((g f : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V), hκ⟩ : ↥(latticeCocycles T₂.L)) =
        ∑ j, bF.equivFun f j • (⟨((g (bF j) : ↥(latticeFiniteCocycles PD T₂.L)) : G → T₂.V), hcZj j⟩ : ↥(latticeCocycles T₂.L)) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      conv_lhs => rw [← bF.sum_equivFun f]
      rw [map_sum, Submodule.coe_sum]
      simp only [map_smul, Submodule.coe_smul]
    show W.clK T₂ (⟨(y f, z f), hmem⟩ : ↥(herrZ1Δ (W.γD T₂ W.gamK) (W.φD T₂) W.DelF (W.γD T₂))) = _
    rw [hx, map_sum, hsum]
    simp only [map_smul, hclj, ← Submodule.mkQ_apply, map_sum]
  · let sA : LetA O n → (W.DD T₂ →ₗ[O] W.DD T₂) := fun c =>
      ((c • LinearMap.id : W.DD T₂ →ₗ[LetA O n] W.DD T₂)).restrictScalars O
    have hsA : ∀ c x, sA c x = c • x := fun c x => by
      simp only [sA, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hNs : ∀ (c : O) (x : W.DD T₂), x ∈ W.N T₂ → c • x ∈ W.N T₂ := fun c x h => by
      rw [← algebraMap_smul (LetA O n) c x]; exact (W.N T₂).smul_mem _ h
    have hJs : ∀ (c : O) (x : W.DD T₂), x ∈ pullJ W T₂ (i - 1) 1 → c • x ∈ pullJ W T₂ (i - 1) 1 :=
      fun c x h => by rw [← algebraMap_smul (LetA O n) c x]; exact Submodule.smul_mem _ _ h
    let Φ4 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • (sA (letE i) ∘ₗ y) + (W.φD T₂ ∘ₗ μ (i - 1)) - μ i
    have hΦ4 : ∀ f', Φ4 f' = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f') + W.φD T₂ (μ (i - 1) f') -
        μ i f' := fun f' => by
      simp only [Φ4, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
    have hΦ4b : ∀ j, Φ4 (bF j) = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • yj j) +
        W.φD T₂ (μj j (i - 1)) - μj j i := fun j => by rw [hΦ4, hyb, hμb, hμb]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact extData_lin (DL W T₂ i) ⟨smul_zero _, fun δ _ => map_zero _⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ c hx)
        bF (μ i) (fun j => by rw [hμb]; exact (hRelj j i).1) f
    · exact extData_lin (DL W T₂ i) ⟨smul_zero _, fun δ _ => map_zero _⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ c hx)
        bF (ν i) (fun j => by rw [hνb]; exact (hRelj j i).2.1) f
    · let Φ3 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • (sA (letE i) ∘ₗ z) + ((W.γ T₂) ∘ₗ μ i - μ i)
      have hΦ3 : ∀ f', Φ3 f' = ((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z f') +
          (W.γ T₂ (μ i f') - μ i f') := fun f' => by
        simp only [Φ3, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
      rw [← hΦ3]
      exact extData_lin (InPN W T₂ 1) ⟨0, (W.N T₂).zero_mem, fun δ _ => map_zero _, (smul_zero _).symm⟩
        (fun x y hx hy => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ hx hy) (fun c x hx => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ c hx)
        bF Φ3 (fun j => by rw [hΦ3, hzb, hμb]; exact (hRelj j i).2.2.1) f
    · have := extData_lin (fun x => x ∈ W.N T₂) (W.N T₂).zero_mem (fun x y hx hy => (W.N T₂).add_mem hx hy)
        hNs bF (sA (qp W ^ Mi i) ∘ₗ Φ4) (fun j => by
          rw [LinearMap.comp_apply, hsA, hΦ4b]; exact (hRelj j i).2.2.2.1) f
      rwa [LinearMap.comp_apply, hsA, hΦ4] at this
    · have := extData_lin (fun x => ∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T₂ (i - 1) 1)
        ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
        (fun x y ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => ⟨s₁ + s₂, by
          simp only [smul_add, pow_add, mul_smul]
          rw [smul_comm (((PD.p : ℕ) : O) ^ s₁) (((PD.p : ℕ) : O) ^ s₂) x]
          exact Submodule.add_mem _ (hJs _ _ h₁) (hJs _ _ h₂)⟩)
        (fun c x ⟨s₀, h₀⟩ => ⟨s₀, by rw [smul_comm]; exact hJs c _ h₀⟩)
        bF (sA (qp W ^ hi i) ∘ₗ Φ4) (fun j => by
          rw [LinearMap.comp_apply, hsA, hΦ4b]; exact (hRelj j i).2.2.2.2.1) f
      rwa [LinearMap.comp_apply, hsA, hΦ4] at this
    · let Φ6 : FF →ₗ[O] W.DD T₂ := ((PD.p : ℕ) : O) ^ N • ν i - sA (qp W ^ a) ∘ₗ μ i
      have hΦ6 : ∀ f', Φ6 f' = ((PD.p : ℕ) : O) ^ N • ν i f' - qp W ^ a • μ i f' := fun f' => by
        simp only [Φ6, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, hsA]
      rw [← hΦ6]
      exact extData_lin (fun x => x ∈ W.N T₂) (W.N T₂).zero_mem (fun x y hx hy => (W.N T₂).add_mem hx hy)
        hNs bF Φ6 (fun j => by rw [hΦ6, hνb, hμb]; exact (hRelj j i).2.2.2.2.2) f

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
