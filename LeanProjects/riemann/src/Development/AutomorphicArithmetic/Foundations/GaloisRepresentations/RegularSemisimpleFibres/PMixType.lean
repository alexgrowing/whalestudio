import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem inj_comp {F R : Type} [Field F] [Field R] (Θ : R →* ℂ) (hΘ : Inj Θ) (e : F →+* R) :
    Inj (Θ.comp e.toMonoidHom) := by
  intro x y hx hy hxy
  have hx' : e x ≠ 0 := by simpa using hx
  have hy' : e y ≠ 0 := by simpa using hy
  exact e.injective (hΘ _ _ hx' hy' hxy)

private theorem cast_eq_of_pow {k : Type} [Field k] [Finite k] (θ : AlgebraicClosure k →* ℂ) (hθ : Inj θ)
    (c c' : ℕ) (h : ∀ u : kˣ, θ (algebraMap k _ (u : k)) ^ c = θ (algebraMap k _ (u : k)) ^ c') :
    ((c : ℕ) : ZMod (Nat.card k - 1)) = ((c' : ℕ) : ZMod (Nat.card k - 1)) := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf ζ = Nat.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have hz : algebraMap k (AlgebraicClosure k) (ζ : k) ≠ 0 := by simp
  have h1 : θ (algebraMap k (AlgebraicClosure k) (ζ : k) ^ c) = θ (algebraMap k (AlgebraicClosure k) (ζ : k) ^ c') := by
    rw [map_pow θ, map_pow θ]; exact h ζ
  have h2 := hθ _ _ (pow_ne_zero _ hz) (pow_ne_zero _ hz) h1
  have h3 : ζ ^ c = ζ ^ c' := by
    apply Units.ext
    apply (algebraMap k (AlgebraicClosure k)).injective
    simpa using h2
  rw [pow_eq_pow_iff_modEq, hord] at h3
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

theorem UpperTheory.Gal.InertialTypesAlt.mixType :
    (LblOn fun _ => True) → LblMixed → SepOf → LeTop → PolTop → TypeOfLbl → ResEmbEx → BaseQ → CardRes → MixType := by
  intro hOn hMix hSep hTop hPol hType hEmb hBase hCard E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hM f hf hs
  obtain ⟨⟨e, he⟩, Θ, hΘ⟩ := hEmb E Ω A v h
  obtain ⟨⟨e', he'⟩, -⟩ := hEmb Y.K Ω A w h'
  obtain ⟨a, s, ha, hApart, hS, hL⟩ := hMix E Ω A v h g i hi (Θ.comp e.toMonoidHom) (inj_comp Θ hΘ e) n τ hM
  obtain ⟨b, hab, hb⟩ := hOn E Ω n hn (Pt.base Ω π) Y hY A Θ hΘ hI v w h h' e e' he he' τ τ' hτ hτ' a trivial ha
  have hag : a.q = g := ha.2.1.trans (hBase E v g i hi).2.1
  have hbQ : b.q = g ^ f := by rw [hb.2.1, hCard, hf]
  have hb2 : 2 ≤ b.q := hb.1.1
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [hbQ, h0] at hb2; simp at hb2
    · exact h0
  have hsp : a.Splits b.q := ⟨f, hf0, by rw [hbQ, hag], fun p hp => by
    obtain ⟨y, hy, hyp⟩ := hL p hp
    rw [← hyp]; exact hs s hS y hy⟩
  obtain ⟨-, -, hL1, hbl⟩ := hTop a b ha.1 hab hsp
  have hsep : b.Sep b.q := by
    have := hSep a b.q ha.1 hApart hsp
    unfold Lbl.Sep at this ⊢
    rwa [hbl]
  obtain ⟨c, d, k, hd, ω, hlist, hω, hT⟩ := hType _ (Θ.comp e'.toMonoidHom) n _ τ'.ρ b hb hL1
  have hbl2 := (hPol b 1 hb2 hL1 (one_pow _)).1
  have hinj : Function.Injective fun x : Fin c => ((k x : ℕ) : ZMod (b.q - 1)) := by
    unfold Lbl.Sep at hsep
    rw [hbl2, hlist.symm] at hsep
    rw [Multiset.map_coe, Multiset.coe_nodup] at hsep
    simp only [List.map_ofFn] at hsep
    exact List.nodup_ofFn.1 hsep
  have : Finite 𝓀[w.adicCompletion Y.K] := Nat.finite_of_card_ne_zero (by rw [← hb.2.1]; omega)
  refine ⟨c, d, hd, ω, ?_, ?_, hT⟩
  · intro x
    have hmem : (d x, k x) ∈ b.D ++ b.L := by
      rw [← hlist]; exact (List.mem_ofFn' _ _).2 ⟨x, rfl⟩
    rcases List.mem_append.1 hmem with hm | hm
    · exact hb.1.2.1 _ hm
    · exact (hb.1.2.2 _ hm).1
  · intro x x' hxx
    apply hinj
    have := cast_eq_of_pow (Θ.comp e'.toMonoidHom) (inj_comp Θ hΘ e') (k x) (k x') (fun u => by
      rw [← hω x u, ← hω x' u, hxx])
    rw [← hb.2.1] at this
    exact this
