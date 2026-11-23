import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateEigenLatticeEqStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PredualVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRankStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IdealSaturatedVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateOmegaCoherentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGlueOverPrimesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcVb

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

theorem isVBOn_of_isVB {L : Lat ξ Li} {r : ℕ} {V : Submodule Ω Li} (h : L.IsVB r V) (T : Set (Cpt ξ)) :
    L.IsVBOn T r V := fun p _ => by
  obtain ⟨U, hU, b, hb, hf⟩ := h p trivial
  exact ⟨U, hU, b, hb, fun q _ hq => hf q trivial hq⟩

theorem integers_regular {F : Type} [Field F] [NumberField F] (hN : Flat.NormalCpt ξ) (σ : 𝓞 F →+* Ω) (q : Cpt ξ)
    (a : 𝓞 F) : σ a ∈ regAt ξ q := by
  refine hN q _ ?_
  have h : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
  exact h.tower_top

theorem unitAt_nat {q : Cpt ξ} [CharZero Ω] (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simpa using Flat.ZUnit.one
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact Flat.ZUnit.mul (ha (left_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_right b))
      (hb (right_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_left a))

theorem unitAt_natAbs_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q (((discr F).natAbs : ℕ) : Ω) :=
  unitAt_nat _ (Int.natAbs_ne_zero.2 (discr_ne_zero F)) fun p hp hd =>
    h p hp (Int.natCast_dvd.2 hd)

theorem unitAt_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q ((discr F : ℤ) : Ω) := by
  have hu := unitAt_natAbs_discr h
  rcases Int.natAbs_eq (discr F) with e | e
  · rw [e]; simpa using hu
  · rw [e]
    simp only [Int.cast_neg, Int.cast_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    exact ⟨neg_ne_zero.2 hu.1, neg_mem hu.2.1, by rw [inv_neg]; exact neg_mem hu.2.2⟩

theorem natAbs_discr_mem_different (F : Type) [Field F] [NumberField F] :
    (((discr F).natAbs : ℕ) : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
  have h := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 F))
  rwa [absNorm_differentIdeal F] at h

variable {G : Over X} [GrpObj G]

theorem lat_stable (M : LieModel G ξ Li) (a : G ⟶ G) [IsMonHom a] (A : Li →ₗ[Ω] Li) (h : M.IsDiffOf a A)
    (p : Cpt ξ) (e : Li) (he : e ∈ M.lat p) : A e ∈ M.lat p := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    refine Submodule.subset_span ⟨v ≫ a, ?_, ?_⟩
    · have h1 := hv.1
      unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left]
      simp [Hom.one_def]
    · rw [h x, Over.comp_left, hv.2, Over.comp_left]
      exact Category.assoc _ _ _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : A (c • x) = c • A x := by
      show A ((c : Ω) • x) = (c : Ω) • A x
      rw [map_smul]
    rw [this]
    exact (M.lat p).smul_mem c hx

end GlobalTheory.CompanionTheory.Ar.HcVb

namespace GlobalTheory.CompanionTheory.Ar.HcVb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

theorem exists_genWeil (hW : Out.WeilSt) {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c)
    (t : SAB H X) (m : SABMap t Y.t f) (hj : ξ ≫ f = y₀ ≫ Y.j) (n : ℕ) (hn : 1 ≤ n)
    (ht : FullTorsion t.G ξ n) (hζ : ∃ ζ : Ω, IsPrimitiveRoot ζ n) : ∃ e, GenWeil t.G t.PP.L ξ n e := by
  obtain ⟨PP', cub, sym, adj, prim, n₁, -⟩ := sabPull Out.proved_CubePullSt ξ t
  obtain ⟨n₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n₁
  rw [hj] at n₂
  obtain ⟨n₃, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n₂
  have := GlobalTheory.T.exists_generic_weil_pairing hW E H D l _ _ _ X _ (GlobalTheory.ModelCompare.objOfSABMap Y.oF n₃) t ξ n₁ Ω (𝟙 _) n hn
    (by rwa [Category.id_comp]) hζ
  rwa [Category.id_comp] at this

end GlobalTheory.CompanionTheory.Ar.HcVb

namespace GlobalTheory.CompanionTheory.Ar

theorem hodgeLattices_isVB : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (cst : c.F →+* Ω) (S : Finset ℕ) (R : ℕ → ℕ) [IsLocallyNoetherian X], ξ ≫ f = y₀ ≫ Y.j → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → IsCptGen ξ → Flat.NormalCpt ξ → (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, FullTorsion t.G ξ (p ^ R p)) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ R p)) → (∀ p ∈ S, ∀ s, ((M.htOm t.PP.L (p ^ R p)).map (eigSp ρ (cst.comp (labelEmb c s))).dualRestrict).IsVB (labelRk D s) ⊤) → ∀ s, (Lat.patch S (M.eigLat ρ (cst.comp (labelEmb c s))) fun p => htLabel M t.PP.L (p ^ R p) ρ (fun s' => cst.comp (labelEmb c s')) s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s))) := by
  intro hW E _ _ _ H D l Xo c Y X Ω _ _ ξ f y₀ t m Li _ _ M ρ cst S R _ hj hs hact hgen hN hSp hdisc htors hζ hVB s
  classical
  have hsm : Smooth t.G.hom := t.semi.smooth
  obtain ⟨hLat, -⟩ := GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ t.G Li M hgen hsm
  obtain ⟨hfd, hrk⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y X Ω ξ f y₀ t m Li M ρ cst hj hs hact
  obtain ⟨hinj, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
  haveI := hfd
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω) := fun s' => cst.comp (labelEmb c s')
  have hσinj : Function.Injective σ := fun a b hab => hinj (RingHom.ext fun x => cst.injective (RingHom.congr_fun hab x))
  have hreg : ∀ (τ : 𝓞 E →+* Ω) (q : Cpt ξ) (a : 𝓞 E), τ a ∈ regAt ξ q :=
    fun τ q a => HcVb.integers_regular hN τ q a
  letI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _

  have hA : (M.eigLat ρ (σ s)).IsVBOn {q | ∀ l ∈ S, ¬ InFibre ξ l q} (labelRk D s) (eigSp ρ (σ s)) := by
    have h := (GlobalTheory.T.lattice_eigen_vector_bundle X Ω ξ Li E ρ M.lat {q | ∀ l ∈ S, ¬ InFibre ξ l q} (Module.finrank Ω Li)
      (CMType H ⊕ CMType H) σ hgen hσinj (by rw [← Nat.card_eq_fintype_card]; exact hcard)
      (HcVb.isVBOn_of_isVB hLat _)
      (fun p _ a e he => by
        haveI := t.act.hom a
        exact HcVb.lat_stable M (t.act.act a) (ρ a) (hact a) p e he)
      (fun p _ s' a => hreg _ p a)
      (fun p hp => HcVb.unitAt_discr fun r hr hd => not_not.1 (hp r (hdisc r hr hd)))).1 s
    rw [hrk s] at h
    exact h

  have hDual : ∀ p ∈ S, ∀ (T : Set (Cpt ξ)) (s' : CMType H ⊕ CMType H),
      (M.htDual t.PP.L (p ^ R p) ρ (σ s')).IsVBOn T (labelRk D s') (eigSp ρ (σ s')) := by
    intro p hp T s'
    have e : M.htDual t.PP.L (p ^ R p) ρ (σ s') = (M.htOm t.PP.L (p ^ R p)).predualIn (eigSp ρ (σ s')) := by
      funext q
      ext v
      exact M.mem_htDual_iff t.PP.L (p ^ R p) ρ (σ s') q v
    rw [e]
    exact GlobalTheory.T.predual_vector_bundle X Ω ξ Li _ T _ _ (HcVb.isVBOn_of_isVB (hVB p hp s') T)
  have hB : ∀ p ∈ S, ∀ (T : Set (Cpt ξ)),
      (htLabel M t.PP.L (p ^ R p) ρ σ s).IsVBOn T (labelRk D s) (eigSp ρ (σ s)) := by
    intro p hp T
    cases s with
    | inr τ => exact hDual p hp T (.inr τ)
    | inl τ =>
      have hσ1 : Function.Injective (σ (.inl τ)) := by
        intro a b hab
        have h1 := cst.injective hab
        have h2 : τ.1 (a : E) = τ.1 (b : E) := congrArg Subtype.val h1
        exact RingOfIntegers.ext (τ.1.injective h2)
      exact GlobalTheory.T.ideal_saturated_vector_bundle X Ω ξ Li (𝓞 E) (σ (.inl τ)) (differentIdeal ℤ (𝓞 E)) _ T _ _
        hσ1 differentIdeal_ne_bot (fun q _ a => hreg _ q a) (hDual p hp T (.inl τ))

  have hC : ∀ p ∈ S, ∀ q : Cpt ξ, (∀ l' : ℕ, l'.Prime → ¬ InFibre ξ l' q) →
      htLabel M t.PP.L (p ^ R p) ρ σ s q = M.eigLat ρ (σ s) q := by
    intro p hp q hq
    have hpp := hSp p hp
    have hn : 1 ≤ p ^ R p := Nat.one_le_pow _ _ hpp.pos
    obtain ⟨e, he⟩ := HcVb.exists_genWeil hW Y ξ f y₀ t m hj (p ^ R p) hn (htors p hp) (hζ p hp)
    have hco := GlobalTheory.T.hodge_tate_omega_coherent X Ω ξ hgen hN t.G t.semi t.PP.L (p ^ R p) hn (htors p hp) e he Li M
    obtain ⟨h1, h2, -⟩ := hco.2 q
    have hu : unitAt ξ q ((p ^ R p : ℕ) : Ω) := by
      rw [Nat.cast_pow]
      exact Flat.ZUnit.pow (not_not.1 (hq p hpp)) _
    have heq : M.htOm t.PP.L (p ^ R p) q = M.omLat q := le_antisymm h2 fun u hu' => by
      have h3 := (M.htOm t.PP.L (p ^ R p) q).smul_mem (⟨((p ^ R p : ℕ) : Ω)⁻¹, hu.2.2⟩ : regAt ξ q) (h1 u hu')
      have e2 : (⟨((p ^ R p : ℕ) : Ω)⁻¹, hu.2.2⟩ : regAt ξ q) • ((p ^ R p) • u) = u := by
        show ((p ^ R p : ℕ) : Ω)⁻¹ • ((p ^ R p) • u) = u
        rw [← Nat.cast_smul_eq_nsmul Ω, inv_smul_smul₀ hu.1]
      rwa [e2] at h3
    obtain ⟨g1, g2⟩ := GlobalTheory.T.hodge_tate_eigen_lattice_eq X Ω ξ t.G Li M t.PP.L (p ^ R p) (Module.finrank Ω Li) (𝓞 E) ρ (σ s) q
      (HcVb.isVBOn_of_isVB hLat _) heq
    rcases s with τ | τ
    · refine g2 _ (fun a => hreg _ q a) ⟨_, HcVb.natAbs_discr_mem_different E, ?_⟩
      rw [map_natCast]
      exact HcVb.unitAt_natAbs_discr fun r hr _ => not_not.1 (hq r hr)
    · exact g1
  obtain ⟨L, hL, hL0, hLp⟩ := GlobalTheory.T.lattice_glue_over_primes X Ω ξ Li S (M.eigLat ρ (σ s))
    (fun p => htLabel M t.PP.L (p ^ R p) ρ σ s) (labelRk D s) (eigSp ρ (σ s)) hgen hSp hA
    (fun p hp => hB p hp _) hC
  have e : Lat.patch S (M.eigLat ρ (σ s)) (fun p => htLabel M t.PP.L (p ^ R p) ρ σ s) = L := by
    funext q
    by_cases h : ∃ p ∈ S, InFibre ξ p q
    · obtain ⟨p, hp, hq⟩ := h
      rw [Lat.patch_of_unique S _ _ hp hq fun p' hp' h' => inFibre_unique (hSp _ hp) (hSp _ hp') hq h',
        hLp p hp q hq]
    · have h' : ∀ p ∈ S, ¬ InFibre ξ p q := fun p hp hf => h ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ h', hL0 q h']
  show (Lat.patch S (M.eigLat ρ (σ s)) fun p => htLabel M t.PP.L (p ^ R p) ρ σ s).IsVB (labelRk D s) (eigSp ρ (σ s))
  rw [e]
  exact hL

end GlobalTheory.CompanionTheory.Ar
