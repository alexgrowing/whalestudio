import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiGS
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.FrSNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.HomBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.LevUp
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.StarSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ChebFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PLNormal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.arPl : ArPl := by
  intro hC l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ hO _ n r hS
  haveI : CharP (ResidueField O) l := hO.char
  have hphi : PhiCond V0.frame.Γ l := phiGS hC.gf l L Ω s V0
  refine ⟨hphi, ?_⟩
  intro q sg hsg
  obtain ⟨H, hH⟩ := hEx l V0.frame O n r
  obtain ⟨W, hWH, hWlim⟩ := frat l V0.frame.Γ H hphi
  have hlift : ∀ x : V0.frame.G₀, ∃ g : G L Ω, V0.pr g = x := by
    intro x
    obtain ⟨g', hg'⟩ := QuotientGroup.mk'_surjective (NS Ω V0.S') (show GS Ω V0.S' from x.1)
    have hr : g' ∈ (resP L Ω).range := by
      rw [← V0.hη g']
      have e : (toGS Ω V0.S') g' = (show GS Ω V0.S' from x.1) := hg'
      rw [e]
      exact x.2
    obtain ⟨g, rfl⟩ := hr
    exact ⟨g, Subtype.ext hg'⟩
  choose g hg using fun j => hlift (sg j)
  let ρ : G L Ω →* V0.frame.Γ := V0.η.ker.subtype.comp V0.pr
  have hρc : Continuous ρ := (continuous_toGS Ω V0.S').comp continuous_resP
  let U : ℕ → Subgroup (G L Ω) := fun N =>
    ((W N).toOpenSubgroup : Subgroup V0.frame.Γ).comap ρ ⊓ (cycMod L Ω l N).ker
  have hUo : ∀ N, IsOpen (U N : Set (G L Ω)) := by
    intro N
    refine IsOpen.inter ((W N).toOpenSubgroup.isOpen.preimage hρc) ?_
    have h1 := (isOpen_discrete ({1} : Set (ZMod (l ^ N)))).preimage
      (GlobalTheory.TameQuot.continuous_cycMod (F := L) (Ω := Ω) l N)
    have e : ((cycMod L Ω l N).ker : Set (G L Ω)) =
        (fun x => ((cycMod L Ω l N x : (ZMod (l ^ N))ˣ) : ZMod (l ^ N))) ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff,
        Units.val_eq_one]
    change IsOpen ((cycMod L Ω l N).ker : Set (G L Ω))
    rw [e]
    exact h1
  have hSfin : s.S.Finite := hS ▸ V0.fin
  choose v w B σ hinj hP using fun N => chebFam L Ω (U N) q (fun j => (g j)⁻¹) s.S (hUo N) hSfin
  have hlw : ∀ N j, (l : 𝓞 L) ∉ (w N j).asIdeal := by
    intro N j hl
    apply (hP N j).1
    left
    rw [← (hP N j).2.2.1]
    rw [← (hP N j).2.1] at hl
    simpa using hl
  have hTQ := fun N j => hC.tame.1 L Ω l (B N j) (w N j) (hP N j).2.1 (hlw N j)
  choose τ hτ using fun N j => (hTQ N j).2.2.2.2.1
  choose VN hVS hN hNe using fun N => levUp l L Ω s V0 O n r (Set.range (v N)) (Set.finite_range _)
    (by rintro _ ⟨j, rfl⟩; exact ⟨B N j, (hP N j).2.2.1, (hP N j).2.2.2.1⟩)
  have hK := fun N => kerLe l L Ω s V0 (VN N) O n r (hN N) (H.toOpenSubgroup : Subgroup V0.frame.Γ)
    q (v N) (B N) (τ N) (hNe N) (hVS N)
    (fun j => ⟨by rw [hS]; exact (hP N j).1, (hP N j).2.2.1, (hP N j).2.2.2.1, hτ N j⟩)
  have hcg : ∀ j, cycZ L Ω l (g j) = 1 := by
    intro j
    have h1 : cycZ L Ω l (g j) = V0.ε (toGS Ω V0.S' (resP L Ω (g j))) := by
      rw [← MonoidHom.comp_apply, V0.hε]
      rfl
    rw [h1]
    have h2 := hsg j
    rw [← hg j] at h2
    exact h2
  have hNq : ∀ N j, normV (w N j) ≡ 1 [MOD l ^ N] := by
    intro N j
    have hu := (hP N j).2.2.2.2.2
    simp only [inv_inv] at hu
    have hk : cycMod L Ω l N (σ N j * g j) = 1 := (Subgroup.mem_inf.1 hu).2
    have hgm : cycMod L Ω l N (g j) = 1 := by simp [cycMod, hcg j]
    rw [map_mul, hgm, mul_one] at hk
    have hz := cycZ_toZModPow_eq (hlw N j) (hP N j).2.1 (hP N j).2.2.2.2.1.2 N
    have hk' : PadicInt.toZModPow N ((cycZ L Ω l (σ N j) : ℤ_[l])) = 1 := by
      have := congrArg Units.val hk
      simpa [cycMod] using this
    rw [hk', map_natCast] at hz
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
    exact hz.symm
  have hWm : ∀ N j, (show V0.frame.Γ from (hN N).p ((VN N).pr (σ N j)⁻¹).1) * ((sg j).1)⁻¹ ∈ W N := by
    intro N j
    have e1 : (hN N).p ((VN N).pr (σ N j)⁻¹).1 = ρ (σ N j)⁻¹ := hNe N (resP L Ω (σ N j)⁻¹)
    have e2 : (sg j).1 = ρ (g j) := by
      rw [← hg j]
      rfl
    rw [e1, e2]
    have hu := (hP N j).2.2.2.2.2
    simp only [inv_inv] at hu
    have hm : ρ (σ N j * g j) ∈ W N := (Subgroup.mem_inf.1 hu).1
    have hc := (W N).isNormal'.conj_mem _ hm (ρ (g j))
    have hi := Subgroup.inv_mem _ hc
    have eq : ρ (σ N j)⁻¹ * (ρ (g j))⁻¹ = (ρ (g j) * ρ (σ N j * g j) * (ρ (g j))⁻¹)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [eq]
    exact hi
  have htame : ∀ N j, ((((VN N).pr (τ N j)) ^ normV (w N j))⁻¹ *
      (((VN N).pr (σ N j)⁻¹)⁻¹ * (VN N).pr (τ N j) * (VN N).pr (σ N j)⁻¹)).1 ∈
      PL l (Subgroup.comap (hN N).p (H.toOpenSubgroup : Subgroup V0.frame.Γ)) := by
    intro N j
    have hσD : σ N j ∈ Dec (B N j) := (hP N j).2.2.2.2.1.1
    have hτD : τ N j ∈ Dec (B N j) := Ine_le_Dec _ (hτ N j).1
    have ht := ((hTQ N j).2.2.2.2.2 ⟨σ N j, hσD⟩ ⟨τ N j, hτD⟩ (hP N j).2.2.2.2.1 (hτ N j)).2.1
    have hm := (hK N).2.1 j _ ht
    have e : (((VN N).pr (τ N j)) ^ normV (w N j))⁻¹ *
        (((VN N).pr (σ N j)⁻¹)⁻¹ * (VN N).pr (τ N j) * (VN N).pr (σ N j)⁻¹) =
        (VN N).pr (((⟨τ N j, hτD⟩ : Dec (B N j)) ^ normV (w N j))⁻¹ *
          ((⟨σ N j, hσD⟩ : Dec (B N j)) * ⟨τ N j, hτD⟩ * (⟨σ N j, hσD⟩ : Dec (B N j))⁻¹) : Dec (B N j)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, map_mul, map_inv, map_pow, inv_inv]
    rw [e]
    exact hm
  let T : TWGrp (globOf r V0) :=
    { q := q
      H := H
      H_η := fun x hx => by
        obtain ⟨h1, -, -⟩ := (hH x).1 hx
        exact h1
      H_ε := fun x hx => by
        obtain ⟨-, -, h3⟩ := (hH x).1 hx
        exact h3
      GN := fun N => globOf r (VN N)
      h := hN
      sg := sg
      sg_mem := hsg
      Nq := fun N j => normV (w N j)
      Nq_mod := hNq
      ph := fun N j => (VN N).pr (σ N j)⁻¹
      ta := fun N j => (VN N).pr (τ N j)
      ph_lim := fun V j hV => (hWlim V hV).mono fun N hle => hle (hWm N j)
      ph_H := fun N j => hWH N (hWm N j)
      ta_ker := fun N j => (hK N).1 j _ (hτ N j).1
      tame := htame
      ker_le := fun N => (hK N).2.2
      hb := Nat.card (HomL l (H.toOpenSubgroup : Subgroup V0.frame.Γ)) *
        l ^ (q * (H.toOpenSubgroup : Subgroup V0.frame.Γ).index)
      fin0 := hphi _ H.toOpenSubgroup.isOpen
      finN := fun N => homBound l (VN N).frame.Γ V0.frame.Γ (hN N).p H q (fun j => ((VN N).pr (τ N j)).1) (hN N).cont
        (hN N).surj (fun j => (hK N).1 j _ (hτ N j).1) ((hK N).2.2) (hphi _ H.toOpenSubgroup.isOpen)
      phiV := fun x => phiDec hC.lf l L Ω (s.A x.1) (s.w x.1) (s.hw x.1)
      phiU := fun u => phiDec hC.lf l L Ω (s.A u.1) (s.w u.1) (s.hw u.1) }
  refine ⟨T, ⟨{
      V := VN
      e := fun N =>
        { p := MonoidHom.id _
          cont := continuous_id
          surj := Function.surjective_id
          η := fun _ => rfl
          c := rfl
          ε := fun _ => rfl
          φ := fun _ _ => rfl
          φu := fun _ _ => rfl }
      e_inj := fun N => Function.injective_id
      e_h := fun N x => hNe N x
      v := v
      v_inj := hinj
      v_not := fun N j => (hP N j).1
      S_eq := fun N => by rw [hVS N, hS]
      w := w
      B := B
      B_w := fun N j => (hP N j).2.1
      B_v := fun N j => (hP N j).2.2.1
      split := fun N j => (hP N j).2.2.2.1
      Nq := fun N j => rfl
      fr := fun N j => (σ N j)⁻¹
      fr_dec := fun N j => inv_mem (hP N j).2.2.2.2.1.1
      fr_frob := fun N j => by simpa using (hP N j).2.2.2.2.1
      τ := τ
      τ_gen := hτ
      ph := fun N j => rfl
      ta := fun N j => rfl
      H_eq := hH }⟩, rfl, fun j => rfl⟩
