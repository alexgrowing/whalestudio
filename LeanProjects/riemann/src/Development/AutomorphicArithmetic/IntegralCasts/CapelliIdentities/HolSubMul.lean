import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe28.FDSec :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] →
            {r : Nat} → {Comp : Type} → (Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r) → Type :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
        [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {r : Nat} {Comp : Type}
        (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r) ↦
      (c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex

noncomputable def UpperTheory.Reformulated.B.Qe28.IsHolCusp :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] →
            {r : Nat} →
              {Comp : Type} →
                (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r) →
                  ((c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r) →
                    @UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X → Prop :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
        [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {r : Nat} {Comp : Type}
        (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r)
        (la : (c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r)
        (P : @UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) ↦
      ∀ (c : Comp),
        @Membership.mem
          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
          (Set (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex))
          (@Set.instMembership
            (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex))
          (@ReciprocityTheory.ChartRestriction.G.FD.Data.SS E inst inst_1 inst_2 r (X c) (la c)) (P c)

noncomputable def UpperTheory.Reformulated.B.Qe28.holSub :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] →
            {r : Nat} →
              {Comp : Type} →
                (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r) →
                  ((c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r) →
                    @Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                      (@Pi.addCommMonoid Comp
                        (fun (c : Comp) ↦
                          @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                            Complex)
                        fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      (@Pi.module Comp
                        (fun (c : Comp) ↦
                          @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                            Complex)
                        Complex Complex.instSemiring
                        (fun (i : Comp) ↦
                          @Pi.addCommMonoid
                            (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                            (fun
                                (a :
                                  @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                    r) ↦
                              Complex)
                            fun
                              (i :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex.instAddCommMonoid)
                        fun (i : Comp) ↦
                        @Pi.Function.module
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          Complex Complex Complex.instSemiring Complex.instAddCommMonoid
                          (@Semiring.toModule Complex Complex.instSemiring)) :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
        [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {r : Nat} {Comp : Type}
        (X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r)
        (la : (c : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r) ↦
      @Submodule.span Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
        (@Pi.addCommMonoid Comp
          (fun (c : Comp) ↦
            @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
          fun (i : Comp) ↦
          @Pi.addCommMonoid (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
            (fun (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦ Complex)
            fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
            Complex.instAddCommMonoid)
        (@Pi.module Comp
          (fun (c : Comp) ↦
            @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
          Complex Complex.instSemiring
          (fun (i : Comp) ↦
            @Pi.addCommMonoid (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
              (fun (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                Complex)
              fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
              Complex.instAddCommMonoid)
          fun (i : Comp) ↦
          @Pi.Function.module (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
            Complex Complex Complex.instSemiring Complex.instAddCommMonoid
            (@Semiring.toModule Complex Complex.instSemiring))
        (@Set.ofPred (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
          fun (P : @UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) ↦
          @UpperTheory.Reformulated.B.Qe28.IsHolCusp E inst inst_1 inst_2 r Comp X la P)

theorem UpperTheory.Reformulated.B.Qe28.holSub_mul :
    ∀ {E : Type} [inst : Field E] [inst_1 : @NumberField E inst]
      [inst_2 : @NumberField.IsCMField E inst (@NumberField.to_charZero E inst inst_1)] {r : Nat},
      @ReciprocityTheory.ChartRestriction.G.FD.SiegelSpaceAlgebra E inst inst_1 inst_2 →
        ∀ {Comp : Type} {X : Comp → @ReciprocityTheory.ChartRestriction.G.FD.Data E inst inst_1 inst_2 r}
          {la la' : (k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r}
          {P Q : @UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X},
          @Membership.mem (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
              (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                (@Pi.addCommMonoid Comp
                  (fun (c : Comp) ↦
                    @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                  fun (i : Comp) ↦
                  @Pi.addCommMonoid
                    (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                    (fun (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex)
                    fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                    Complex.instAddCommMonoid)
                (@Pi.module Comp
                  (fun (c : Comp) ↦
                    @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                  Complex Complex.instSemiring
                  (fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  fun (i : Comp) ↦
                  @Pi.Function.module
                    (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                    Complex Complex.instSemiring Complex.instAddCommMonoid
                    (@Semiring.toModule Complex Complex.instSemiring)))
              (@SetLike.instMembership
                (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                  (@Pi.addCommMonoid Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  (@Pi.module Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    Complex Complex.instSemiring
                    (fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    fun (i : Comp) ↦
                    @Pi.Function.module
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                      Complex Complex.instSemiring Complex.instAddCommMonoid
                      (@Semiring.toModule Complex Complex.instSemiring)))
                (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                (@Submodule.setLike Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                  (@Pi.addCommMonoid Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  (@Pi.module Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    Complex Complex.instSemiring
                    (fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    fun (i : Comp) ↦
                    @Pi.Function.module
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                      Complex Complex.instSemiring Complex.instAddCommMonoid
                      (@Semiring.toModule Complex Complex.instSemiring))))
              (@UpperTheory.Reformulated.B.Qe28.holSub E inst inst_1 inst_2 r Comp X la) P →
            @Membership.mem (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                  (@Pi.addCommMonoid Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  (@Pi.module Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    Complex Complex.instSemiring
                    (fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    fun (i : Comp) ↦
                    @Pi.Function.module
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                      Complex Complex.instSemiring Complex.instAddCommMonoid
                      (@Semiring.toModule Complex Complex.instSemiring)))
                (@SetLike.instMembership
                  (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                    (@Pi.addCommMonoid Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    (@Pi.module Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      Complex Complex.instSemiring
                      (fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      fun (i : Comp) ↦
                      @Pi.Function.module
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                        Complex Complex.instSemiring Complex.instAddCommMonoid
                        (@Semiring.toModule Complex Complex.instSemiring)))
                  (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@Submodule.setLike Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                    (@Pi.addCommMonoid Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    (@Pi.module Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      Complex Complex.instSemiring
                      (fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      fun (i : Comp) ↦
                      @Pi.Function.module
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                        Complex Complex.instSemiring Complex.instAddCommMonoid
                        (@Semiring.toModule Complex Complex.instSemiring))))
                (@UpperTheory.Reformulated.B.Qe28.holSub E inst inst_1 inst_2 r Comp X la') Q →
              @Membership.mem (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                  (@Pi.addCommMonoid Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    fun (i : Comp) ↦
                    @Pi.addCommMonoid
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                      (fun
                          (a : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex)
                      fun (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                      Complex.instAddCommMonoid)
                  (@Pi.module Comp
                    (fun (c : Comp) ↦
                      @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r → Complex)
                    Complex Complex.instSemiring
                    (fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    fun (i : Comp) ↦
                    @Pi.Function.module
                      (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                      Complex Complex.instSemiring Complex.instAddCommMonoid
                      (@Semiring.toModule Complex Complex.instSemiring)))
                (@SetLike.instMembership
                  (@Submodule Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                    (@Pi.addCommMonoid Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    (@Pi.module Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      Complex Complex.instSemiring
                      (fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      fun (i : Comp) ↦
                      @Pi.Function.module
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                        Complex Complex.instSemiring Complex.instAddCommMonoid
                        (@Semiring.toModule Complex Complex.instSemiring)))
                  (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@Submodule.setLike Complex (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X) Complex.instSemiring
                    (@Pi.addCommMonoid Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.addCommMonoid
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instAddCommMonoid)
                    (@Pi.module Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      Complex Complex.instSemiring
                      (fun (i : Comp) ↦
                        @Pi.addCommMonoid
                          (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                          (fun
                              (a :
                                @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))
                                  r) ↦
                            Complex)
                          fun
                            (i :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex.instAddCommMonoid)
                      fun (i : Comp) ↦
                      @Pi.Function.module
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) Complex
                        Complex Complex.instSemiring Complex.instAddCommMonoid
                        (@Semiring.toModule Complex Complex.instSemiring))))
                (@UpperTheory.Reformulated.B.Qe28.holSub E inst inst_1 inst_2 r Comp X
                  (@HAdd.hAdd
                    ((k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                    ((k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                    ((k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                    (@instHAdd
                      ((k : Comp) → @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                      (@Pi.instAdd Comp
                        (fun (k : Comp) ↦
                          @ReciprocityTheory.ChartRestriction.G.FD.Wt E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X k)) r)
                        fun (i : Comp) ↦
                        @Pi.instAdd (↥(@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)))
                          (fun (a : ↥(@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))) ↦ Fin r → Int)
                          fun (i : ↥(@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i))) ↦
                          @Pi.instAdd (Fin r) (fun (a : Fin r) ↦ Int) fun (i : Fin r) ↦ Int.instAdd))
                    la la'))
                (@HMul.hMul (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                  (@instHMul (@UpperTheory.Reformulated.B.Qe28.FDSec E inst inst_1 inst_2 r Comp X)
                    (@Pi.instMul Comp
                      (fun (c : Comp) ↦
                        @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X c)) r →
                          Complex)
                      fun (i : Comp) ↦
                      @Pi.instMul
                        (@ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r)
                        (fun
                            (a :
                              @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                          Complex)
                        fun
                          (i : @ReciprocityTheory.ChartRestriction.G.FD.Frame E inst (@ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ E inst inst_1 inst_2 r (X i)) r) ↦
                        Complex.instMul))
                  P Q) := by
  intro E _ _ _ r h5 Comp X la la' P Q hP hQ
  have key : ∀ (l : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (R : UpperTheory.Reformulated.B.Qe28.FDSec X),
      R ∈ UpperTheory.Reformulated.B.Qe28.holSub X l → UpperTheory.Reformulated.B.Qe28.IsHolCusp X l R := by
    intro l R hR
    induction hR using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun c => (h5 r (X c) (l c) (l c) 0).1.1
    | add x y _ _ hx hy => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.1 _ (hx c) _ (hy c)
    | smul a x _ hx => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.2 a _ (hx c)
  exact Submodule.subset_span fun c =>
    (h5 r (X c) (la c) (la' c) 0).2.1 _ (key la P hP c) _ (key la' Q hQ c).1
