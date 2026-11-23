import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_block (hBC : UpperTheory.Gal.TypesAndIwahori.BlockCount) {s N : ℕ} (d c : Fin s → ℕ) (hd : ∑ a, d a = N) (y : ℂ) :
    ∏ j : Fin N, (X - C (y ^ c (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)) : ℂ[X]) =
      ∏ a, (X - C (y ^ c a)) ^ d a := by
  show (Finset.univ.val.map fun j => (fun a => (X - C (y ^ c a) : ℂ[X])) (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)).prod = _
  rw [hBC ℂ[X] N s d hd (fun a => X - C (y ^ c a)), Multiset.prod_sum]
  simp [Multiset.prod_replicate]

private theorem pol_top (hBC : UpperTheory.Gal.TypesAndIwahori.BlockCount) (hPT : PolTop) (b : Lbl) {s N : ℕ} (d c : Fin s → ℕ)
    (hd : ∑ a, d a = N) (hl : List.ofFn (fun a => (d a, c a)) = b.D ++ b.L) (y : ℂ) (h2 : 2 ≤ b.q)
    (h1 : ∀ p ∈ b.L, p.1 = 1) (hy : y ^ (b.q - 1) = 1) :
    ∏ j : Fin N, (X - C (y ^ c (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j)) : ℂ[X]) = b.pol b.q y := by
  rw [prod_block hBC, (hPT b y h2 h1 hy).2, ← hl, List.map_ofFn, List.prod_ofFn]
  rfl

private theorem pol_bot (hPB : PolBot) (q Q : ℕ) {s : ℕ} (m c : Fin s → ℕ) (y : ℂ) (h2 : 2 ≤ Q) (hy : y ^ (Q - 1) = 1) :
    (⟨q, [], List.ofFn fun a => (m a, c a)⟩ : Lbl).pol Q y =
      ∏ a, ∏ j ∈ Finset.range (m a), (X - C (y ^ (c a * q ^ j * ((Q - 1) / (q ^ m a - 1))))) := by
  rw [hPB q Q _ y h2 hy, List.map_ofFn, List.prod_ofFn]
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.suppAny :
    (LblOn fun a => a.D = []) → LblOf → TypeOfLbl → UpperTheory.Gal.TypesAndIwahori.SuppOfType → UpperTheory.Gal.TypesAndIwahori.BlockCount → TameChars → LeTop → PolTop → PolBot → ResEmbEx → UnifTower → BaseQ → CardRes → ArtRead → CuspIne → SuppIne → SuppAny := by
  intro hOn hOf hTy hSO hBC hTC hLT hPT hPB hRE hUT hBQ hCR hAR hCI hSI
  intro E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hD f hf hs
  haveI : CharZero (v.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w.adicCompletion Y.K) := charZero_of_injective_algebraMap (algebraMap Y.K _).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨⟨e, he⟩, Θ, hΘ⟩ := hRE E Ω A v h
  obtain ⟨⟨e', he'⟩, -⟩ := hRE Y.K Ω A w h'
  have eqv : τ.ρ.Equiv (IrrGL.of τ.ρ τ.smooth τ.irred).rep := IrrGL.equivOf _ _ _
  obtain ⟨𝔪, hm⟩ := UpperTheory.Zero.LLC.Pr.exh (v.adicCompletion E) (IrrGL.of τ.ρ τ.smooth τ.irred)
  have hS₀ : HasSupport (IrrGL.of τ.ρ τ.smooth τ.irred).rep (msupp 𝔪) :=
    hasSupport_msupp_of_isL UpperTheory.Zero.LLC.Pr.zel _ 𝔪 _ hm
  have hS : HasSupport τ.ρ (msupp 𝔪) := hS₀.of_equiv eqv.symm
  have hfix : fixed τ.ρ (KOne (v.adicCompletion E) (Fin n)) ≠ ⊥ := GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv eqv.symm hD
  have hθ : Inj (Θ.comp e.toMonoidHom) := fun a b ha hb hab =>
    e.injective (hΘ _ _ (by simpa using ha) (by simpa using hb) hab)
  obtain ⟨hg2, hcard, -⟩ := hBQ E v g i hi
  obtain ⟨s, x, c, hxS, hx, hlbl⟩ := hOf _ (Θ.comp e.toMonoidHom) hθ n _ τ.ρ _ hS hfix
  rw [hcard] at hlbl hx
  obtain ⟨b, hab, hb⟩ := hOn E Ω n hn (Pt.base Ω π) Y hY A Θ hΘ hI v w h h' e e' he he' τ τ' hτ hτ' _ rfl hlbl
  have hbq : b.q = g ^ f := by rw [hb.2.1, hCR, hf]
  have hb2 : 2 ≤ b.q := hb.1.1
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h0
    · simp [hbq] at hb2
    · exact h0
  have hdiv : ∀ a, (x a).1 ∣ f := fun a =>
    hs _ hS _ (by rw [← hxS]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ a))
  have hsp : (⟨g, [], List.ofFn fun a => ((x a).1, c a)⟩ : Lbl).Splits b.q := by
    refine ⟨f, hf0, hbq, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hp
    exact hdiv a
  obtain ⟨-, -, hL1, hblk⟩ := hLT _ b hlbl.1 hab hsp
  obtain ⟨s', d, c', hd, ω, hl, hω, hTV⟩ := hTy _ (Θ.comp e'.toMonoidHom) n _ τ'.ρ b hb hL1
  have hTS := hSO _ n s' d hd _ τ'.ρ τ'.smooth τ'.irred ω hTV
  obtain ⟨ξ, hξ, hξt, hξs, hξu⟩ := hTC _ n _ τ'.ρ _ hTS
  refine ⟨ξ, hξ, hξt, hξs, ?_⟩
  intro rc hrc a' ha' t
  have hQ : 1 ≤ normV w - 1 := by rw [hf, ← hbq]; omega
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Ω, ϖ ^ (normV w - 1) = (g : Ω) := IsAlgClosed.exists_pow_nat_eq _ hQ
  have hg1 : ((g : ℕ) : 𝓞 Y.K) ∈ w.asIdeal := DiscreteGroups.sglob.DzType.natCast_mem_of_normV w g f hf0 hf
  have hg2' : ((g : ℕ) : 𝓞 Y.K) ∉ w.asIdeal ^ 2 := hUT E Ω n (Pt.base Ω π) Y hY A hI v w h h' g hg2
  obtain ⟨z, u, hz, hu, hres, hpow⟩ := hAR Y.K Ω A w h' g hg1 hg2' a' ha' e' he' t ϖ hϖ
  obtain ⟨y, hyd⟩ : ∃ y : ℂ, y = Θ (IsLocalRing.residue A z) := ⟨_, rfl⟩
  have hy : y ^ (g ^ f - 1) = 1 := by rw [hyd, ← map_pow, ← hf, hpow, map_one]
  have hξ' : ∀ j, ((ξ j (a' (ineIncl h' t)) : ℂˣ) : ℂ) = y ^ c' (UpperTheory.Gal.TypesAndIwahori.blockOf d hd j) := by
    intro j
    rw [← hu, hξu, hω, hyd, ← hres]
    rfl
  let t₀ : Ine (F := E) A := ⟨AlgEquiv.restrictScalars E (t : G Y.K Ω), t.2.1, t.2.2⟩
  have hcu : ∀ a, (rc (x a)).inePol (t₀ : G E Ω) =
      ∏ j ∈ Finset.range (x a).1, (X - C (y ^ (c a * g ^ j * ((g ^ f - 1) / (g ^ (x a).1 - 1))))) := by
    intro a
    rw [hyd]
    exact hCI E Ω A v h g i hi Θ hΘ e (x a) (c a) (hx a).1 (hx a).2.1 (hx a).2.2.1 (hx a).2.2.2 rc hrc f hf0 (hdiv a)
      t₀ ϖ (hf ▸ hϖ) z hz
  have hSx : HasSupport (IrrGL.of τ.ρ τ.smooth τ.irred).rep (msupp 𝔪) := hS₀
  have h1 := hSI E Ω A v h rc hrc _ _ hSx t₀
  rw [← hxS, Multiset.map_map] at h1
  have h2 : (rc (IrrGL.of τ.ρ τ.smooth τ.irred)).inePol (t₀ : G E Ω) =
      ∏ a, ∏ j ∈ Finset.range (x a).1, (X - C (y ^ (c a * g ^ j * ((g ^ f - 1) / (g ^ (x a).1 - 1))))) := by
    rw [h1, ← Finset.prod_congr rfl fun a _ => hcu a]
    rfl
  have h3 := pol_top hBC hPT b d c' hd hl y hb2 hL1 (hbq ▸ hy)
  have h4 := pol_bot hPB g (g ^ f) (fun a => (x a).1) c y (hbq ▸ hb2) hy
  have h5 : b.pol (g ^ f) y = (⟨g, [], List.ofFn fun a => ((x a).1, c a)⟩ : Lbl).pol (g ^ f) y := by
    rw [← hbq]
    unfold Lbl.pol
    rw [hblk]
  rw [hbq, h5, h4] at h3
  simp only [hξ']
  exact h2.trans h3.symm
