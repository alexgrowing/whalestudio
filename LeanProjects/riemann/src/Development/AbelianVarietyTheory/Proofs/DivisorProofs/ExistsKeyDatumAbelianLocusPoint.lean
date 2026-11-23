import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfSubsetAbLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullMulAddPullMulInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyDatumAb

theorem exists_keyOn : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing B] (f : A →+* B) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)), 1 ≤ g → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsOpen (abLocus G) → L.IsSymmetric → PolOnAb G L.L → IsLieBasis y → NzFib σ → Set.range (spMap f) ⊆ abLocus G → ∃ (x : KeyIn B) (hg : x.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) := by
  intro A B _ _ _ _ _ f G _ _ L σ g y hg1 hG hd hO hs hpol hy hσ hr
  let W : (Sp A).Opens := ⟨abLocus G, hO⟩
  have hWsub : (W : Set (Sp A)) ⊆ abLocus G := subset_rfl
  have hprop : IsProper (G.hom ∣_ W) := GlobalTheory.AbLocusProperNormal.isProper_restrict_of_subset_abLocus A G hG W hWsub
  have hGW : IsAbelianScheme ((Over.pullback W.ι).obj G) := GlobalTheory.SquareSemiOpen.isAb_pullback_open G hG W hprop
  haveI : IsProper ((Over.pullback W.ι).obj G).hom := hGW.proper
  obtain ⟨ha, hk⟩ := hpol W hWsub
  obtain ⟨x', hx'⟩ : ∃ x' : Sp B ⟶ W.toScheme, x' ≫ W.ι = spMap f :=
    ⟨IsOpenImmersion.lift W.ι (spMap f) (by rw [Scheme.Opens.range_ι]; exact hr), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G (spMap f)
  have h₀ := isGrpPullback_pullback G W.ι
  have h₂ := h.congr hx'.symm rfl
  let φ : ((Over.pullback (spMap f)).obj G).left ⟶ G.left := pullback.fst G.hom (spMap f)
  let ψ : ((Over.pullback (spMap f)).obj G).left ⟶ ((Over.pullback W.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom W.ι = φ := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback (spMap f)).obj G) ((Over.pullback W.ι).obj G) x' ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB L.isLB φ
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom W.ι)
  obtain ⟨w, hw⟩ : LBIso (L.L.pull φ) ((L.L.pull (pullback.fst G.hom W.ι)).pull ψ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => φ) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl hL)
  have hamp₀ : RelAmple (Over.mk ((Over.pullback (spMap f)).obj G).hom) ((L.L.pull (pullback.fst G.hom W.ι)).pull ψ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL₀ ha h₃.1
  have hLψ := pull_isLB hL₀ ψ
  obtain ⟨w', hw'⟩ : LBIso (L.L.pull φ) (((L.L.pull (pullback.fst G.hom W.ι)).pull ψ).pull (𝟙 _)) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl) ⟨w, hw⟩
  have hamp : RelAmple ((Over.pullback (spMap f)).obj G) (L.L.pull φ) :=
    relAmple_pull (A' := (Over.pullback (spMap f)).obj G) (A := Over.mk ((Over.pullback (spMap f)).obj G).hom)
      (IsPullback.id_horiz _) hLψ hL ((isGen_iff w').1 hw') ⊤ (isAffineOpen_top _) (fun _ => trivial) hamp₀
  have hsa := IsSemiAbelian.pullback (spMap f) G hG
  have hA : IsAbelianScheme ((Over.pullback (spMap f)).obj G) :=
    { comm := hsa.comm, smooth := hsa.smooth,
      proper := MorphismProperty.of_isPullback (P := @IsProper) h₃.1 hGW.proper
      geomConnected := hsa.geomConnected }
  haveI := hsa.comm
  let P : PolAV (Sp B) :=
    { A := (Over.pullback (spMap f)).obj G
      isAb := hA
      g := g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hd
      L := L.L.pull φ
      isLB := hL
      rigid := PolBaseChange.rigidified_pull h ⟨L.rig, L.rigGen⟩
      sym := PolBaseChange.sym_pull h (CechPic.sym_of_isSymmetric L hs)
      ample := hamp
      ktriv := kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk }
  have he : eSec P.A ≫ φ = spMap f ≫ eSec G := PolBaseChange.eSec_comm h
  have hr' : (rigPullOf φ (spMap f) he L.L L.rig).IsGen :=
    Out.LBxP.isGen_pullAlong L.L φ (spMap f) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec P.A)
      (fun _ => he) L.rig L.rigGen
  have hw0 := (isGen_iff _).1 (idIso_isGen hL)
  obtain ⟨th', hth'⟩ := sec_pull_down hw0 L.isLB hL σ
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.exists_isLieBasis_baseChange A B f G P.A φ h hG.smooth g y hy
  have := hA.smooth
  refine ⟨⟨P, hg1, _, hr', th', fun s => ?_, v', hv'⟩, rfl, φ, he, idIso _, Chart.dualMapR f, h, idIso_isGen hL,
    fun p => hr' p.1 p.2, GlobalTheory.KeyPow.appLE_eq_of_stalk _ σ th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv'φ i⟩
  · obtain ⟨z, hz, hz'⟩ := hσ (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (σ.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyDatumAb
